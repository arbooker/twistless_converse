module
public meta import QuantitativeArithmeticCompactCommandsV1
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic
public import QuantitativeArithmeticMonomialCancellationV1
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3285_10 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*((x)*((-1:ℂ)*a)) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*((y^(2:ℕ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3285_18 (x y z a b : ℂ) :
    ((1:ℂ))*((x*a)*(y^(2:ℕ) + (1:ℂ))) = (x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ)*y^(2:ℕ) + (-1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*0 := by ring1

compact_certificate theorem combination0_3285_20 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*0 := by ring1

compact_certificate theorem combination0_3285_30 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ))) + (x^(2:ℕ)*a^(2:ℕ))*0 := by ring1

compact_certificate theorem combination0_3285_42 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (1:ℂ))) = (x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*(((1:ℂ))*(x*a + (1:ℂ))) + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*0 := by ring1

compact_certificate theorem combination0_3285_5 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + (x^(2:ℕ)*a^(2:ℕ))*0 := by ring1

compact_certificate theorem combination0_3285_62 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*0 := by ring1

compact_certificate theorem combination0_3285_72 (x y z a b : ℂ) :
    ((1:ℂ))*((x^(2:ℕ))*((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a + (-1:ℂ)*a^(2:ℕ) + (1:ℂ))) = (x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*((x)*(x + a)) + ((-1:ℂ))*((x)*((-1:ℂ)*x)) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*(((1:ℂ))*((-1:ℂ))) := by ring1

compact_certificate theorem combination0_3285_84 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*((x*a)*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3288_42 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*(x^(2:ℕ) + x*a + (1:ℂ))) = ((1:ℂ))*((x^(2:ℕ))*((1:ℂ))) + ((1:ℂ))*(((1:ℂ))*(x*a + (1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ))*0 := by ring1

compact_certificate theorem combination0_3288_54 (x y z a b : ℂ) :
    ((1:ℂ))*0 = ((1:ℂ))*(((1:ℂ))*((1:ℂ))) + ((1:ℂ))*0 + ((-1:ℂ))*0 + ((-1:ℂ))*(((1:ℂ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3288_72 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*(x^(2:ℕ) + x*a + (1:ℂ))) = ((1:ℂ))*0 + ((1:ℂ))*((x)*(x + a)) + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ))*0 := by ring1

compact_certificate theorem combination0_3288_84 (x y z a b : ℂ) :
    ((1:ℂ))*0 = ((1:ℂ))*((x)*((-1:ℂ)*a)) + ((1:ℂ))*((x*a)*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ))*0 := by ring1

compact_certificate theorem combination0_3288_99 (x y z a b : ℂ) :
    ((1:ℂ))*0 = ((1:ℂ))*((x^(2:ℕ))*((1:ℂ))) + ((1:ℂ))*0 + ((-1:ℂ))*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3290_104 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*((x)*((-1:ℂ)*a)) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3290_109 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + (x^(2:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3290_18 (x y z a b : ℂ) :
    ((1:ℂ))*((x*a)*((-1:ℂ)*y^(2:ℕ) + (-1:ℂ))) = (x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*(y^(2:ℕ) + (1:ℂ))) + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3290_30 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) := by ring1

compact_certificate theorem combination0_3290_42 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ) + (-1:ℂ)*x*a + (-1:ℂ))) = (x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*(((1:ℂ))*(x*a + (1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3290_52 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3290_72 (x y z a b : ℂ) :
    ((1:ℂ))*((x)*(x^(3:ℕ) + (-1:ℂ)*x + (-1:ℂ)*a)) = (x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*((x)*(x + a)) + ((-1:ℂ)*x^(2:ℕ))*((x)*((-1:ℂ)*x)) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3290_84 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ))) + (x^(2:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3290_94 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ)*x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + (x^(2:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3590_18 (x y z a b : ℂ) :
    (x*a)*0 = (x*a)*0 + ((-1:ℂ))*((x^(3:ℕ)*a)*(x^(2:ℕ) + x*a + (1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*(((1:ℂ))*((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a + (-1:ℂ))) := by ring1

compact_certificate theorem combination0_3590_30 (x y z a b : ℂ) :
    (x*a)*0 = (x*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3590_36 (x y z a b : ℂ) :
    (x*a)*0 = (x*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*(((1:ℂ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3590_42 (x y z a b : ℂ) :
    (x*a)*(((1:ℂ))*((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a + (-1:ℂ))) = (x*a)*0 + ((-1:ℂ))*(((1:ℂ))*(x^(3:ℕ)*a + x^(2:ℕ)*a^(2:ℕ) + x*a + (1:ℂ))) + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3590_72 (x y z a b : ℂ) :
    (x*a)*(((1:ℂ))*((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a + (-1:ℂ))) = (x*a)*((x)*((-1:ℂ)*a)) + ((-1:ℂ))*((x)*(x^(2:ℕ)*a + x + a)) + ((-1:ℂ))*((x)*((-1:ℂ)*x)) + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3590_93 (x y z a b : ℂ) :
    (x*a)*0 = (x*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*((x^(3:ℕ)*a)*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3775_15 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*((y)*((-1:ℂ)*b)) + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x*y*a*b)*((x^(2:ℕ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3775_16 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ)*y^(2:ℕ))) + (x*y*a*b)*0 := by ring1

compact_certificate theorem combination0_3775_18 (x y z a b : ℂ) :
    ((1:ℂ))*((x*a)*(x^(8:ℕ)*y^(2:ℕ) + x^(7:ℕ)*y^(2:ℕ)*a + x^(6:ℕ)*y^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(4:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y^(4:ℕ) + x^(2:ℕ) + y^(2:ℕ) + (1:ℂ))) = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*((x*a)*((-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + y^(2:ℕ))) + ((-1:ℂ)*x^(2:ℕ)*a)*((a)*(x^(6:ℕ) + x^(5:ℕ)*a + x^(4:ℕ) + x^(3:ℕ)*a + x^(2:ℕ)*a^(2:ℕ) + x*a)) + ((-1:ℂ)*x^(2:ℕ)*a)*((x)*((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a + (-1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*(((1:ℂ))*((-1:ℂ)*x*a + (-1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x*y*a*b)*0 := by ring1

compact_certificate theorem combination0_3775_30 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + (x*y*a*b)*0 := by ring1

compact_certificate theorem combination0_3775_42 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*(x^(7:ℕ)*y^(2:ℕ)*a + x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(6:ℕ)*a^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y^(2:ℕ) + x^(3:ℕ)*y^(3:ℕ)*a*b + x^(3:ℕ)*y^(2:ℕ)*a + x^(2:ℕ)*y^(3:ℕ)*b + x^(2:ℕ)*y*a^(2:ℕ)*b + (1:ℂ))) = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (-1:ℂ)*x*a + (-1:ℂ)*y*b)) + ((-1:ℂ)*x^(2:ℕ)*a)*(((1:ℂ))*(x^(3:ℕ)*a^(2:ℕ) + x^(2:ℕ)*a + x + a)) + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x*y*a*b)*(((1:ℂ))*((-1:ℂ))) := by ring1

compact_certificate theorem combination0_3775_43 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*((x*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x*y*a*b)*0 := by ring1

compact_certificate theorem combination0_3775_45 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*((x^(2:ℕ))*((1:ℂ))) + (x*y*a*b)*0 := by ring1

compact_certificate theorem combination0_3775_5 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + (x*y*a*b)*0 := by ring1

compact_certificate theorem combination0_3775_72 (x y z a b : ℂ) :
    ((1:ℂ))*((x^(2:ℕ))*(x^(5:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y^(2:ℕ) + x^(4:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + x^(2:ℕ)*y^(3:ℕ)*b + x*y^(3:ℕ)*a*b + (-1:ℂ)*x*y^(2:ℕ)*a + x*y*a*b + y*a^(2:ℕ)*b + (-1:ℂ)*a^(2:ℕ) + (1:ℂ))) = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*((x)*((-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*b + (-1:ℂ)*y*a*b + a)) + ((-1:ℂ)*x^(2:ℕ)*a)*(((1:ℂ))*(x^(3:ℕ) + x^(2:ℕ)*a)) + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*((x)*((-1:ℂ)*x)) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x*y*a*b)*0 := by ring1

compact_certificate theorem combination0_3775_81 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x*y*a*b)*0 := by ring1

compact_certificate theorem combination0_3775_86 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*((y^(2:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ)*a)*((y^(2:ℕ))*((-1:ℂ)*a)) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x*y*a*b)*0 := by ring1

compact_certificate theorem combination0_3775_90 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*a)*((x*a)*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*((x^(2:ℕ))*((-1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ)*x*a)) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + (x*y*a*b)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3776_16 (x y z a b : ℂ) :
    (x*a)*0 = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*0 + (x^(3:ℕ)*y*a*b)*0 + (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*(((1:ℂ))*((-1:ℂ)*y^(2:ℕ))) := by ring1

compact_certificate theorem combination0_3776_18 (x y z a b : ℂ) :
    (x*a)*((x)*(x^(6:ℕ)*y^(2:ℕ)*a + x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a + x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ)*y^(2:ℕ)*a^(3:ℕ) + x^(2:ℕ)*a + x*y^(2:ℕ)*a^(2:ℕ) + x*a^(2:ℕ) + (-1:ℂ)*y^(4:ℕ)*a + a)) = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*((x*a)*((-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + y^(2:ℕ))) + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*((x^(3:ℕ)*a)*(x^(2:ℕ) + x*a + (1:ℂ))) + (x^(3:ℕ)*y*a*b)*0 + (x^(3:ℕ)*a)*((y)*(x^(2:ℕ)*b + x*a*b + b)) + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3776_21 (x y z a b : ℂ) :
    (x*a)*0 = (x^(3:ℕ)*a)*((y)*((-1:ℂ)*b)) + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*0 + (x^(3:ℕ)*y*a*b)*(((1:ℂ))*((1:ℂ))) + (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3776_26 (x y z a b : ℂ) :
    (x*a)*0 = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*0 + (x^(3:ℕ)*y*a*b)*0 + (x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3776_42 (x y z a b : ℂ) :
    (x*a)*(((1:ℂ))*(x^(5:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + x^(2:ℕ)*y^(2:ℕ) + x*y^(3:ℕ)*a*b + x*y^(2:ℕ)*a + (-1:ℂ)*x*y*a*b + y^(3:ℕ)*b + (1:ℂ))) = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (-1:ℂ)*x*a + (-1:ℂ)*y*b)) + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*(((1:ℂ))*(x^(3:ℕ)*a + x^(2:ℕ)*a^(2:ℕ) + x*a + (1:ℂ))) + (x^(3:ℕ)*y*a*b)*(((1:ℂ))*((1:ℂ))) + (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3776_45 (x y z a b : ℂ) :
    (x*a)*0 = (x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*0 + (x^(3:ℕ)*y*a*b)*0 + (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3776_63 (x y z a b : ℂ) :
    (x*a)*0 = (x^(3:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*0 + (x^(3:ℕ)*y*a*b)*0 + (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3776_72 (x y z a b : ℂ) :
    (x*a)*((x)*(x^(4:ℕ)*y^(2:ℕ)*a + x^(3:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y^(2:ℕ)*a + x*y^(3:ℕ)*b + x + y^(3:ℕ)*a*b + (-1:ℂ)*y^(2:ℕ)*a)) = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*((x)*((-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*b + (-1:ℂ)*y*a*b + a)) + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*((x)*(x^(2:ℕ)*a + x + a)) + (x^(3:ℕ)*y*a*b)*(((1:ℂ))*((1:ℂ))) + (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3776_7 (x y z a b : ℂ) :
    (x*a)*0 = (x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*0 + (x^(3:ℕ)*y*a*b)*0 + (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3776_83 (x y z a b : ℂ) :
    (x*a)*0 = (x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*0 + (x^(3:ℕ)*y*a*b)*0 + (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3776_8 (x y z a b : ℂ) :
    (x*a)*0 = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*0 + (x^(3:ℕ)*y*a*b)*0 + (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ)*y^(2:ℕ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3776_90 (x y z a b : ℂ) :
    (x*a)*0 = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*0 + (x^(3:ℕ)*y*a*b)*0 + (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*(((1:ℂ))*((-1:ℂ)*x*a)) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3776_93 (x y z a b : ℂ) :
    (x*a)*0 = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*((x^(3:ℕ)*a)*((1:ℂ))) + (x^(3:ℕ)*y*a*b)*(((1:ℂ))*((1:ℂ))) + (x^(3:ℕ)*a)*(((1:ℂ))*(x^(2:ℕ))) + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3776_99 (x y z a b : ℂ) :
    (x*a)*0 = (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ))*0 + ((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*y*b)*0 + (x^(3:ℕ)*y*a*b)*0 + (x^(3:ℕ)*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3777_10 (x y z a b : ℂ) :
    (x*a)*0 = (x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x)*0 + (y*b)*0 + ((-1:ℂ)*x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3777_18 (x y z a b : ℂ) :
    (x*a)*0 = (x*a)*0 + ((-1:ℂ))*((x*a)*((-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + y^(2:ℕ))) + ((-1:ℂ)*x)*((a)*(x^(6:ℕ) + x^(5:ℕ)*a + x^(4:ℕ) + x^(3:ℕ)*a + x^(2:ℕ)*a^(2:ℕ) + x*a)) + (y*b)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) := by ring1

compact_certificate theorem combination0_3777_30 (x y z a b : ℂ) :
    (x*a)*0 = (x*a)*((y)*((-1:ℂ)*b)) + ((-1:ℂ))*0 + ((-1:ℂ)*x)*0 + (y*b)*((x*a)*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3777_42 (x y z a b : ℂ) :
    (x*a)*(((1:ℂ))*(x^(4:ℕ) + y*b)) = (x*a)*0 + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (-1:ℂ)*x*a + (-1:ℂ)*y*b)) + ((-1:ℂ)*x)*(((1:ℂ))*(x^(3:ℕ)*a^(2:ℕ) + x^(2:ℕ)*a + x + a)) + (y*b)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3777_48 (x y z a b : ℂ) :
    (x*a)*0 = (x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x)*0 + (y*b)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3777_72 (x y z a b : ℂ) :
    (x*a)*(((1:ℂ))*(x^(4:ℕ) + y*b)) = (x*a)*0 + ((-1:ℂ))*((x)*((-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*b + (-1:ℂ)*y*a*b + a)) + ((-1:ℂ)*x)*(((1:ℂ))*(x^(3:ℕ) + x^(2:ℕ)*a)) + (y*b)*((x)*((-1:ℂ)*x)) + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3777_86 (x y z a b : ℂ) :
    (x*a)*0 = (x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x)*((y^(2:ℕ)*a)*((1:ℂ))) + (y*b)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3777_90 (x y z a b : ℂ) :
    (x*a)*0 = (x*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x)*0 + (y*b)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3779_13 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + (y^(2:ℕ))*0 + ((-1:ℂ))*0 + (x*y*a*b)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3779_18 (x y z a b : ℂ) :
    ((1:ℂ))*((x*a)*((-1:ℂ)*x^(6:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y^(2:ℕ)*a + (-1:ℂ)*x*a + y^(4:ℕ) + (-1:ℂ))) = (x^(3:ℕ)*a)*0 + (y^(2:ℕ))*((x*a)*((-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + y^(2:ℕ))) + ((-1:ℂ))*((x*a)*(x^(3:ℕ)*y*a*b + x^(2:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(2:ℕ)*y*b + x^(2:ℕ) + x*y*a*b + x*a + (2:ℂ))) + (x*y*a*b)*((x)*(x^(2:ℕ)*a + x*a^(2:ℕ) + (-1:ℂ)*x + a)) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3779_24 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*0 + (y^(2:ℕ))*0 + ((-1:ℂ))*0 + (x*y*a*b)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3779_39 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*((y)*((-1:ℂ)*b)) + (y^(2:ℕ))*0 + ((-1:ℂ))*0 + (x*y*a*b)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3779_3 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + (y^(2:ℕ))*0 + ((-1:ℂ))*0 + (x*y*a*b)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*(((1:ℂ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3779_42 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x*y^(3:ℕ)*a*b + (-1:ℂ)*x*y^(2:ℕ)*a + x*y*a*b + (-1:ℂ)*y^(3:ℕ)*b + (-1:ℂ))) = (x^(3:ℕ)*a)*0 + (y^(2:ℕ))*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (-1:ℂ)*x*a + (-1:ℂ)*y*b)) + ((-1:ℂ))*(((1:ℂ))*((1:ℂ))) + (x*y*a*b)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3779_51 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + (y^(2:ℕ))*0 + ((-1:ℂ))*0 + (x*y*a*b)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3779_72 (x y z a b : ℂ) :
    ((1:ℂ))*((x)*((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x*y^(3:ℕ)*b + (-1:ℂ)*x + (-1:ℂ)*y^(3:ℕ)*a*b + y^(2:ℕ)*a)) = (x^(3:ℕ)*a)*0 + (y^(2:ℕ))*((x)*((-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*b + (-1:ℂ)*y*a*b + a)) + ((-1:ℂ))*((x^(2:ℕ))*((1:ℂ))) + (x*y*a*b)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3779_89 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + (y^(2:ℕ))*0 + ((-1:ℂ))*((x^(3:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + (x*y*a*b)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3779_90 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*a)*0 + (y^(2:ℕ))*((x*a)*((1:ℂ))) + ((-1:ℂ))*0 + (x*y*a*b)*0 + ((-1:ℂ)*x*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3780_12 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*y^(2:ℕ))*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3780_14 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*y^(2:ℕ))*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*a)*0 := by ring1

compact_certificate theorem combination0_3780_18 (x y z a b : ℂ) :
    ((1:ℂ))*((x*a)*(x^(6:ℕ)*y^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ) + x*y^(2:ℕ)*a + x*a + (-1:ℂ)*y^(4:ℕ) + (1:ℂ))) = (x*a)*0 + ((-1:ℂ)*y^(2:ℕ))*((x*a)*((-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + y^(2:ℕ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a + (-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 := by ring1

compact_certificate theorem combination0_3780_30 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*a)*0 + ((-1:ℂ)*y^(2:ℕ))*0 + ((-1:ℂ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 := by ring1

compact_certificate theorem combination0_3780_36 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*a)*0 + ((-1:ℂ)*y^(2:ℕ))*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 := by ring1

compact_certificate theorem combination0_3780_42 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*(x^(5:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + x^(2:ℕ)*y^(2:ℕ) + x*y^(3:ℕ)*a*b + x*y^(2:ℕ)*a + (-1:ℂ)*x*y*a*b + y^(3:ℕ)*b + (1:ℂ))) = (x*a)*((y)*((-1:ℂ)*b)) + ((-1:ℂ)*y^(2:ℕ))*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (-1:ℂ)*x*a + (-1:ℂ)*y*b)) + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 := by ring1

compact_certificate theorem combination0_3780_52 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*y^(2:ℕ))*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 := by ring1

compact_certificate theorem combination0_3780_72 (x y z a b : ℂ) :
    ((1:ℂ))*((x)*(x^(4:ℕ)*y^(2:ℕ)*a + x^(3:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y^(2:ℕ)*a + x*y^(3:ℕ)*b + x + y^(3:ℕ)*a*b + (-1:ℂ)*y^(2:ℕ)*a)) = (x*a)*0 + ((-1:ℂ)*y^(2:ℕ))*((x)*((-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*b + (-1:ℂ)*y*a*b + a)) + ((-1:ℂ))*((x)*((-1:ℂ)*x)) + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 := by ring1

compact_certificate theorem combination0_3780_90 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*y^(2:ℕ))*((x*a)*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 + ((-1:ℂ)*x*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3855_103 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + (a)*0 + (x^(5:ℕ)*y*b + x^(5:ℕ) + x^(3:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ))*0 + ((-1:ℂ)*x)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3855_18 (x y z a b : ℂ) :
    ((1:ℂ))*((x*a)*((-1:ℂ)*x^(11:ℕ)*y*b + (-1:ℂ)*x^(11:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(11:ℕ) + (-1:ℂ)*x^(10:ℕ)*y*a*b + (-2:ℂ)*x^(10:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(10:ℕ)*a + x^(9:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(9:ℕ)*y*b + (-1:ℂ)*x^(9:ℕ)*a^(4:ℕ) + (-2:ℂ)*x^(9:ℕ) + x^(8:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(8:ℕ)*y*a*b + (-1:ℂ)*x^(8:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(8:ℕ)*a + (-2:ℂ)*x^(7:ℕ)*a^(4:ℕ) + x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(7:ℕ) + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a + x^(6:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(6:ℕ)*y*a*b + (-1:ℂ)*x^(6:ℕ)*a^(5:ℕ) + (-2:ℂ)*x^(6:ℕ)*a^(3:ℕ) + x^(5:ℕ)*y^(3:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ) + x^(5:ℕ)*y*a^(4:ℕ)*b + (-2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a + (4:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (-3:ℂ)*x^(4:ℕ)*y*a*b + x^(4:ℕ)*z*a + (-1:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(3:ℕ)*a^(2:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ) + (2:ℂ)*x^(3:ℕ)*y*a^(4:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + x^(3:ℕ)*z*a^(2:ℕ) + (2:ℂ)*x^(3:ℕ)*a^(2:ℕ) + x^(2:ℕ)*y^(2:ℕ)*a + x^(2:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(2:ℕ)*y*a*b + (2:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*a^(2:ℕ)*b + (2:ℂ)*x*a^(2:ℕ) + (-1:ℂ)*x + (-1:ℂ)*a)) = (x^(4:ℕ)*y^(2:ℕ)*a)*0 + (a)*((x*a)*((-1:ℂ)*x^(11:ℕ)*a + (-2:ℂ)*x^(10:ℕ)*a^(2:ℕ) + x^(9:ℕ)*y*a*b + (-1:ℂ)*x^(9:ℕ)*a^(3:ℕ) + x^(8:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(8:ℕ)*a^(2:ℕ) + x^(8:ℕ) + x^(7:ℕ)*y*a*b + (-2:ℂ)*x^(7:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ) + x^(6:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(6:ℕ)*y*b + (-1:ℂ)*x^(6:ℕ)*a^(4:ℕ) + (-2:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a + x^(5:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ) + (4:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(4:ℕ)*y*b + x^(4:ℕ)*z + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(3:ℕ)*a*b + (-2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a + (2:ℂ)*x^(3:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*z*a + (2:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (2:ℂ)*x*a + (-1:ℂ))) + (x^(5:ℕ)*y*b + x^(5:ℕ) + x^(3:ℕ))*((x*a)*((-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + y^(2:ℕ))) + ((-1:ℂ)*x^(5:ℕ))*0 + ((-1:ℂ)*x)*((x*a)*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y*a^(2:ℕ)*b + x*y*a*b + (1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3855_24 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*0 + (a)*0 + (x^(5:ℕ)*y*b + x^(5:ℕ) + x^(3:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ))*0 + ((-1:ℂ)*x)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) := by ring1

compact_certificate theorem combination0_3855_42 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(10:ℕ)*y*a*b + (-1:ℂ)*x^(10:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(10:ℕ)*a + (-1:ℂ)*x^(9:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(9:ℕ)*a^(4:ℕ) + x^(8:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(8:ℕ)*y*a*b + (-1:ℂ)*x^(8:ℕ)*a^(5:ℕ) + (-2:ℂ)*x^(8:ℕ)*a + x^(7:ℕ)*y*a^(4:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*y*b + (-2:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(7:ℕ) + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ)*a + (-2:ℂ)*x^(6:ℕ)*y*a*b + (-2:ℂ)*x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*b^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a^(4:ℕ)*b + x^(5:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*b + (-2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + (3:ℂ)*x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(4:ℕ)*a^(5:ℕ) + (3:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(4:ℕ)*a + x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*a*b + (3:ℂ)*x^(2:ℕ)*a + (2:ℂ)*x*a^(2:ℕ) + (-1:ℂ)*x + (-1:ℂ)*a)) = (x^(4:ℕ)*y^(2:ℕ)*a)*0 + (a)*(((1:ℂ))*((-1:ℂ)*x^(10:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(9:ℕ)*a^(3:ℕ) + x^(9:ℕ)*a + x^(8:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(8:ℕ)*a^(4:ℕ) + x^(7:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(3:ℕ)*b + x^(5:ℕ)*y*a*b + (-2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(5:ℕ)*a + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y*b + (-2:ℂ)*x^(4:ℕ)*a^(4:ℕ) + (2:ℂ)*x^(4:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a + x^(3:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y*b + (2:ℂ)*x^(2:ℕ) + (2:ℂ)*x*a + (-1:ℂ))) + (x^(5:ℕ)*y*b + x^(5:ℕ) + x^(3:ℕ))*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (-1:ℂ)*x*a + (-1:ℂ)*y*b)) + ((-1:ℂ)*x^(5:ℕ))*((y^(2:ℕ))*((-1:ℂ)*x*a + (-1:ℂ))) + ((-1:ℂ)*x)*(((1:ℂ))*((-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + (1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3855_46 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + (a)*0 + (x^(5:ℕ)*y*b + x^(5:ℕ) + x^(3:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ))*((x*y^(2:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3855_70 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + (a)*0 + (x^(5:ℕ)*y*b + x^(5:ℕ) + x^(3:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ))*0 + ((-1:ℂ)*x)*((x^(3:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3855_72 (x y z a b : ℂ) :
    ((1:ℂ))*((x)*((-1:ℂ)*x^(9:ℕ)*y*a*b + (-1:ℂ)*x^(9:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(9:ℕ)*a + (-1:ℂ)*x^(8:ℕ)*y*b + (-1:ℂ)*x^(8:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(8:ℕ) + x^(7:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*y*a*b + (-1:ℂ)*x^(7:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*b^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*y*b + (-1:ℂ)*x^(6:ℕ)*a^(4:ℕ) + x^(6:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(3:ℕ)*b + x^(5:ℕ)*y*a*b + (2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y*a^(4:ℕ)*b + (3:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(4:ℕ)*y*b + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + x^(3:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y*a*b + (-3:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (4:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(2:ℕ)*a^(4:ℕ) + (6:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(2:ℕ) + (2:ℂ)*x*a^(3:ℕ) + (-1:ℂ)*x*a + (-1:ℂ)*a^(2:ℕ))) = (x^(4:ℕ)*y^(2:ℕ)*a)*0 + (a)*((x)*((-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ)*a^(3:ℕ) + x^(7:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*a^(3:ℕ) + x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + x^(5:ℕ)*y*b + (2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (3:ℂ)*x^(4:ℕ)*y*a*b + (-2:ℂ)*x^(4:ℕ)*a + x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(3:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*y*b + (-3:ℂ)*x^(3:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*a*b + (-2:ℂ)*x^(2:ℕ)*a^(3:ℕ) + (5:ℂ)*x^(2:ℕ)*a + (2:ℂ)*x*a^(2:ℕ) + (-1:ℂ)*x + (-1:ℂ)*a)) + (x^(5:ℕ)*y*b + x^(5:ℕ) + x^(3:ℕ))*((x)*((-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*b + (-1:ℂ)*y*a*b + a)) + ((-1:ℂ)*x^(5:ℕ))*((x)*((-1:ℂ)*x*y^(2:ℕ) + (-1:ℂ)*y^(2:ℕ)*a + a)) + ((-1:ℂ)*x)*((x^(2:ℕ))*((-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + (-1:ℂ)*a^(2:ℕ) + (1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3855_90 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*0 + (a)*0 + (x^(5:ℕ)*y*b + x^(5:ℕ) + x^(3:ℕ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ))*((x*a)*(y*b + (1:ℂ))) + ((-1:ℂ)*x)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3855_92 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*((x)*((-1:ℂ)*a)) + (a)*((x^(5:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + (x^(5:ℕ)*y*b + x^(5:ℕ) + x^(3:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ))*0 + ((-1:ℂ)*x)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3874_18 (x y z a b : ℂ) :
    ((1))*((x*a)*(x^11*y*a*b + (2)*x^11*a + x^10*y*a^2*b + (3)*x^10*a^2 + x^9*a^3 + x^9*a + (2)*x^8*a^2 + (-2)*x^8 + x^7*y*a^3*b + (-1)*x^7*y*a*b + (3)*x^7*a^3 + (-3)*x^7*a + x^6*y^2 + x^6*y*b + x^6*a^4 + (3)*x^6*a^2 + (-2)*x^6 + (-1)*x^5*y^3*a*b + (-1)*x^5*y*a^3*b + (2)*x^5*a^3 + x^4*y^2 + (-4)*x^4*y*a^2*b + (2)*x^4*y*b + (-1)*x^4*z + x^4*a^2 + (-2)*x^4 + x^3*y^3*a*b + (2)*x^3*y^2*a + (-2)*x^3*y*a^3*b + x^3*y*a*b + (-1)*x^3*z*a + (-2)*x^3*a + (-1)*x^2*y^2 + (-1)*x^2*y*a^2*b + (-2)*x^2 + x*y*a*b + (-2)*x*a + (1))) = (x^5*y^2*a)*0 + ((-1))*((x*a)*((-1)*x^11*a + (-2)*x^10*a^2 + x^9*y*a*b + (-1)*x^9*a^3 + x^8*y*a^2*b + (-1)*x^8*a^2 + x^8 + x^7*y*a*b + (-2)*x^7*a^3 + (2)*x^7*a + (-1)*x^6*y^2 + x^6*y*a^2*b + (-1)*x^6*y*b + (-1)*x^6*a^4 + (-2)*x^6*a^2 + x^6 + (-1)*x^5*y^2*a + x^5*y*a^3*b + (-2)*x^5*a^3 + (-1)*x^4*y^2 + (4)*x^4*y*a^2*b + (-2)*x^4*y*b + x^4*z + (-1)*x^4*a^2 + (2)*x^4 + (-1)*x^3*y^3*a*b + (-2)*x^3*y^2*a + (2)*x^3*y*a^3*b + (-1)*x^3*y*a*b + x^3*z*a + (2)*x^3*a + x^2*y^2 + x^2*y*a^2*b + (2)*x^2 + (-1)*x*y*a*b + (2)*x*a + (-1))) + ((-1)*x^5*y*a*b + (-1)*x^5*a)*((x*a)*((-1)*x^6 + (-1)*x^5*a + (-1)*x^4 + (-1)*x^3*a + (-1)*x^2*a^2 + (-1)*x*a + y^2)) + (x^5*a)*0 + ((-1)*x^7*a)*(((1))*(x^2 + x*a + (1))) := by ring1

compact_certificate theorem combination0_3874_23 (x y z a b : ℂ) :
    ((1))*((x^7*y^2*a)*((1))) = (x^5*y^2*a)*((x^2)*((1))) + ((-1))*0 + ((-1)*x^5*y*a*b + (-1)*x^5*a)*0 + (x^5*a)*0 + ((-1)*x^7*a)*0 := by ring1

compact_certificate theorem combination0_3874_42 (x y z a b : ℂ) :
    ((1))*(((1))*(x^10*y*a^2*b + (2)*x^10*a^2 + x^9*y*a^3*b + (3)*x^9*a^3 + (-1)*x^9*a + x^8*a^4 + x^8*a^2 + (-1)*x^7*y^2*a + (-1)*x^7*y*a^3*b + x^7*y*a*b + (2)*x^7*a + x^6*y^2*a^2*b^2 + (-1)*x^6*y^2*a^2 + (2)*x^6*y*a^2*b + x^6*a^2 + x^5*y^2*a*b^2 + x^5*y*a^3*b + (2)*x^5*a^3 + (-2)*x^5*a + (-1)*x^4*y^2*a^2*b^2 + x^4*y^2*a^2 + (-2)*x^4*y*a^2*b + (-1)*x^4*y*b + (2)*x^4*a^4 + (-2)*x^4*a^2 + (-1)*x^3*y^2*a*b^2 + x^3*y^2*a + (-1)*x^3*y*a*b + x^3*a^3 + x^3*a + x^2*y*b + (-2)*x^2 + (-2)*x*a + (1))) = (x^5*y^2*a)*0 + ((-1))*(((1))*((-1)*x^10*a^2 + (-2)*x^9*a^3 + x^9*a + x^8*y*a^2*b + (-1)*x^8*a^4 + x^7*y*a^3*b + (-1)*x^7*a + (-1)*x^5*y^2*a + (-1)*x^5*y*a^3*b + x^5*y*a*b + (-2)*x^5*a^3 + (2)*x^5*a + x^4*y^2*a^2*b^2 + (-1)*x^4*y^2*a^2 + (2)*x^4*y*a^2*b + x^4*y*b + (-2)*x^4*a^4 + (2)*x^4*a^2 + x^3*y^2*a*b^2 + (-1)*x^3*y^2*a + x^3*y*a*b + (-1)*x^3*a^3 + (-1)*x^3*a + (-1)*x^2*y*b + (2)*x^2 + (2)*x*a + (-1))) + ((-1)*x^5*y*a*b + (-1)*x^5*a)*(((1))*((-1)*x^5*a + (-1)*x^4*a^2 + (-1)*x^3*a + (-1)*x^2 + (-1)*x*y*a*b + (-1)*x*a + (-1)*y*b)) + (x^5*a)*((y^2)*((-1)*x*a + (-1))) + ((-1)*x^7*a)*((y^2)*((1))) := by ring1

compact_certificate theorem combination0_3874_46 (x y z a b : ℂ) :
    ((1))*0 = (x^5*y^2*a)*((x)*((-1)*a)) + ((-1))*0 + ((-1)*x^5*y*a*b + (-1)*x^5*a)*0 + (x^5*a)*((x*y^2*a)*((1))) + ((-1)*x^7*a)*0 := by ring1

compact_certificate theorem combination0_3874_72 (x y z a b : ℂ) :
    ((1))*((x)*(x^9*y*a^2*b + (2)*x^9*a^2 + x^8*y*a*b + x^8*a^3 + x^8*a + (2)*x^7*a^2 + x^6*y^2*a*b^2 + (-1)*x^6*y^2*a + x^6*y*a*b + x^6*a^3 + (-1)*x^6*a + x^5*y^2*a^2*b^2 + (-1)*x^5*y^2*a^2 + x^5*y*a^2*b + (-1)*x^5*y*b + (-2)*x^5*a^2 + (-1)*x^4*y^2*a*b^2 + x^4*y^2*a + x^4*y*a^3*b + (-3)*x^4*y*a*b + (2)*x^4*a + (-1)*x^3*y^2*a^2*b^2 + (-1)*x^3*y*a^2*b + x^3*y*b + (3)*x^3*a^2 + (-2)*x^3 + x^2*y*a*b + (2)*x^2*a^3 + (-5)*x^2*a + (-2)*x*a^2 + x + a)) = (x^5*y^2*a)*0 + ((-1))*((x)*((-1)*x^9*a^2 + (-1)*x^8*a^3 + x^7*y*a^2*b + (-1)*x^7*a^2 + (-1)*x^6*a^3 + x^6*a + (-1)*x^5*y*a^2*b + x^5*y*b + (2)*x^5*a^2 + x^4*y^2*a*b^2 + (-1)*x^4*y^2*a + (-1)*x^4*y*a^3*b + (3)*x^4*y*a*b + (-2)*x^4*a + x^3*y^2*a^2*b^2 + x^3*y*a^2*b + (-1)*x^3*y*b + (-3)*x^3*a^2 + (2)*x^3 + (-1)*x^2*y*a*b + (-2)*x^2*a^3 + (5)*x^2*a + (2)*x*a^2 + (-1)*x + (-1)*a)) + ((-1)*x^5*y*a*b + (-1)*x^5*a)*((x)*((-1)*x^4*a + (-1)*x^3 + (-1)*x^2*a + (-1)*x*y*b + (-1)*y*a*b + a)) + (x^5*a)*((x)*((-1)*x*y^2 + (-1)*y^2*a + a)) + ((-1)*x^7*a)*0 := by ring1

compact_certificate theorem combination0_3874_80 (x y z a b : ℂ) :
    ((1))*0 = (x^5*y^2*a)*((x^2)*((1))) + ((-1))*0 + ((-1)*x^5*y*a*b + (-1)*x^5*a)*0 + (x^5*a)*0 + ((-1)*x^7*a)*((y^2)*((1))) := by ring1

compact_certificate theorem combination0_3874_90 (x y z a b : ℂ) :
    ((1))*0 = (x^5*y^2*a)*0 + ((-1))*0 + ((-1)*x^5*y*a*b + (-1)*x^5*a)*((x*a)*((1))) + (x^5*a)*((x*a)*(y*b + (1))) + ((-1)*x^7*a)*0 := by ring1

compact_certificate theorem combination0_3874_92 (x y z a b : ℂ) :
    ((1))*0 = (x^5*y^2*a)*(((1))*((1))) + ((-1))*((x^5*y^2*a)*((1))) + ((-1)*x^5*y*a*b + (-1)*x^5*a)*0 + (x^5*a)*0 + ((-1)*x^7*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3882_18 (x y z a b : ℂ) :
    ((1))*((x*a)*(x^10*a^3 + (-1)*x^10*a + (-1)*x^9*y*a^2*b + x^9*y*b + x^9*a^4 + (-2)*x^9*a^2 + x^9 + (-1)*x^8*y*a^3*b + x^8*y*a*b + x^8*a + (-1)*x^7*y*a^2*b + x^7*y*b + x^7*a^4 + (-3)*x^7*a^2 + (4)*x^7 + (-1)*x^6*y*a^3*b + x^6*y*a*b + x^6*a^5 + (-2)*x^6*a^3 + (3)*x^6*a + x^5*y^2*a^2 + (-1)*x^5*y^2 + (-1)*x^5*y*a^4*b + (2)*x^5*y*a^2*b + (-1)*x^5*y*b + (2)*x^5*a^4 + (-4)*x^5*a^2 + (3)*x^5 + (-2)*x^4*y*a^3*b + (2)*x^4*y*a*b + x^4*a^3 + (-1)*x^4*a + x^3*y^3*a^2*b + (-1)*x^3*y^3*b + (2)*x^3*y^2*a^2 + (-2)*x^3*y^2 + (-2)*x^3*y*a^4*b + (5)*x^3*y*a^2*b + (-2)*x^3*y*b + (-1)*x^3*z*a^2 + x^3*z + (-2)*x^3*a^2 + (2)*x^3 + (-1)*x^2*y^2*a + (-1)*x^2*y*a^3*b + (2)*x^2*y*a*b + x*y*a^2*b + (-2)*x*a^2 + (2)*x + a)) = (x^4*y^2*a)*0 + (a)*((x*a)*(x^10*a^2 + (-1)*x^9*y*a*b + x^9*a^3 + (-1)*x^9*a + (-1)*x^8*y*a^2*b + x^8 + (-1)*x^7*y*a*b + x^7*a^3 + (-2)*x^7*a + (-1)*x^6*y*a^2*b + x^6*a^4 + (-1)*x^6*a^2 + x^6 + x^5*y^2*a + (-1)*x^5*y*a^3*b + x^5*y*a*b + (2)*x^5*a^3 + (-2)*x^5*a + (-2)*x^4*y*a^2*b + x^4*a^2 + x^3*y^3*a*b + (2)*x^3*y^2*a + (-2)*x^3*y*a^3*b + (3)*x^3*y*a*b + (-1)*x^3*z*a + (-2)*x^3*a + (-1)*x^2*y^2 + (-1)*x^2*y*a^2*b + x*y*a*b + (-2)*x*a + (1))) + ((-1)*x)*((x*a)*(x^9*a + (-1)*x^8*y*b + x^8*a^2 + (-1)*x^8 + (-1)*x^7*y*a*b + (-1)*x^6*y*b + x^6*a^2 + (-3)*x^6 + (-1)*x^5*y*a*b + x^5*a^3 + (-1)*x^5*a + x^4*y^2 + (-1)*x^4*y*a^2*b + x^4*y*b + (2)*x^4*a^2 + (-2)*x^4 + (-2)*x^3*y*a*b + x^3*a + x^2*y^3*b + (2)*x^2*y^2 + (-2)*x^2*y*a^2*b + (2)*x^2*y*b + (-1)*x^2*z + (-2)*x^2 + (-2)*x*y*a*b + (-2))) + ((-1)*x^6*a)*(((1))*((-1)*x^2 + (-1)*x*a + (-1))) := by ring1

compact_certificate theorem combination0_3882_22 (x y z a b : ℂ) :
    ((1))*0 = (x^4*y^2*a)*(((1))*((1))) + (a)*0 + ((-1)*x)*((x^3*y^2*a)*((1))) + ((-1)*x^6*a)*0 := by ring1

compact_certificate theorem combination0_3882_34 (x y z a b : ℂ) :
    ((1))*0 = (x^4*y^2*a)*((x^2)*((1))) + (a)*0 + ((-1)*x)*0 + ((-1)*x^6*a)*((y^2)*((1))) := by ring1

compact_certificate theorem combination0_3882_42 (x y z a b : ℂ) :
    ((1))*(((1))*(x^9*a^4 + (-1)*x^9*a^2 + (-1)*x^8*y*a^3*b + x^8*y*a*b + x^8*a^5 + (-2)*x^8*a^3 + x^8*a + (-1)*x^7*y*a^4*b + x^7*y*a^2*b + x^7*a^2 + (-1)*x^6*y*a^3*b + x^6*y*a*b + x^6*a + x^5*y*a^4*b + (-2)*x^5*y*a^2*b + x^5*y*b + x^5 + (-1)*x^4*y^2*a^3*b^2 + x^4*y^2*a^3 + x^4*y^2*a*b^2 + (-1)*x^4*y^2*a + (-2)*x^4*y*a^3*b + (2)*x^4*y*a*b + (2)*x^4*a^5 + (-6)*x^4*a^3 + (5)*x^4*a + (-1)*x^3*y^2*a^2*b^2 + x^3*y^2*a^2 + x^3*y^2*b^2 + (-1)*x^3*y^2 + (-1)*x^3*y*a^2*b + (2)*x^3*y*b + x^3*a^4 + (-2)*x^3*a^2 + x^3 + x^2*y*a*b + (-1)*x^2*a + (-2)*x*a^2 + (2)*x + a)) = (x^4*y^2*a)*0 + (a)*(((1))*(x^9*a^3 + (-1)*x^8*y*a^2*b + x^8*a^4 + (-1)*x^8*a^2 + (-1)*x^7*y*a^3*b + x^7*a + (-1)*x^6*y*a^2*b + x^5*y*a^3*b + (-1)*x^5*y*a*b + (-1)*x^4*y^2*a^2*b^2 + x^4*y^2*a^2 + (-2)*x^4*y*a^2*b + (2)*x^4*a^4 + (-4)*x^4*a^2 + x^4 + (-1)*x^3*y^2*a*b^2 + x^3*y^2*a + (-1)*x^3*y*a*b + x^3*a^3 + x^2*y*b + (-2)*x*a + (1))) + ((-1)*x)*(((1))*(x^8*a^2 + (-1)*x^7*y*a*b + x^7*a^3 + (-1)*x^7*a + (-1)*x^6*y*a^2*b + (-1)*x^5*y*a*b + (-1)*x^5*a + x^4*y*a^2*b + (-1)*x^4*y*b + (-1)*x^4 + (-1)*x^3*y^2*a*b^2 + x^3*y^2*a + (-2)*x^3*y*a*b + (2)*x^3*a^3 + (-4)*x^3*a + (-1)*x^2*y^2*b^2 + x^2*y^2 + (-2)*x^2*y*b + (2)*x^2*a^2 + (-1)*x^2 + x*a + (-2))) + ((-1)*x^6*a)*0 := by ring1

compact_certificate theorem combination0_3882_68 (x y z a b : ℂ) :
    ((1))*0 = (x^4*y^2*a)*((x)*((-1)*a)) + (a)*((x^5*y^2*a)*((1))) + ((-1)*x)*0 + ((-1)*x^6*a)*0 := by ring1

compact_certificate theorem combination0_3882_72 (x y z a b : ℂ) :
    ((1))*((x)*(x^8*a^4 + (-1)*x^8*a^2 + (-1)*x^7*y*a^3*b + x^7*y*a*b + (-1)*x^6*y*a^2*b + x^6*y*b + x^6*a^4 + (-1)*x^6*a^2 + x^6 + (-1)*x^5*y^2*a + (-2)*x^5*a^3 + (3)*x^5*a + (-1)*x^4*y^2*a^2*b^2 + x^4*y^2*a^2 + x^4*y^2*b^2 + (-1)*x^4*y^2 + x^4*y*a^4*b + (-3)*x^4*y*a^2*b + (2)*x^4*y*b + x^4 + (-1)*x^3*y^2*a^3*b^2 + x^3*y^2*a*b^2 + (-1)*x^3*y*a^3*b + (2)*x^3*y*a*b + x^3*a^3 + (-1)*x^3*a + x^2*y*a^2*b + (2)*x^2*a^4 + (-6)*x^2*a^2 + (2)*x^2 + (-2)*x*a^3 + (2)*x*a + a^2)) = (x^4*y^2*a)*0 + (a)*((x)*(x^8*a^3 + (-1)*x^7*y*a^2*b + (-1)*x^6*y*a*b + x^6*a^3 + (-2)*x^5*a^2 + x^5 + (-1)*x^4*y^2*a*b^2 + x^4*y^2*a + x^4*y*a^3*b + (-2)*x^4*y*a*b + (-1)*x^3*y^2*a^2*b^2 + (-1)*x^3*y*a^2*b + x^3*y*b + x^3*a^2 + x^2*y*a*b + (2)*x^2*a^3 + (-4)*x^2*a + (-2)*x*a^2 + x + a)) + ((-1)*x)*((x)*(x^7*a^2 + (-1)*x^6*y*a*b + (-1)*x^5*y*b + x^5*a^2 + (-1)*x^5 + (-2)*x^4*a + (-1)*x^3*y^2*b^2 + x^3*y^2 + x^3*y*a^2*b + (-2)*x^3*y*b + (-1)*x^3 + (-1)*x^2*y^2*a*b^2 + (-1)*x^2*y*a*b + x^2*a + (2)*x*a^2 + (-2)*x + (-1)*a)) + ((-1)*x^6*a)*((y^2)*((1))) := by ring1

compact_certificate theorem combination0_3882_91 (x y z a b : ℂ) :
    ((1))*((x^6*y^2*a)*((1))) = (x^4*y^2*a)*((x^2)*((1))) + (a)*0 + ((-1)*x)*0 + ((-1)*x^6*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3888_15 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + (x^(4:ℕ)*y*a*b)*0 + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3888_16 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*0 + ((-1:ℂ))*0 + (x^(4:ℕ)*y*a*b)*0 + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*(((1:ℂ))*((-1:ℂ)*y^(2:ℕ))) + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3888_18 (x y z a b : ℂ) :
    ((1:ℂ))*((x*a)*((-1:ℂ)*x^(10:ℕ)*y*a*b + (-1:ℂ)*x^(10:ℕ)*a^(3:ℕ) + x^(10:ℕ)*a + (-1:ℂ)*x^(9:ℕ)*y*b + (-1:ℂ)*x^(9:ℕ)*a^(4:ℕ) + (2:ℂ)*x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(9:ℕ) + x^(8:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(8:ℕ)*y*a*b + (-1:ℂ)*x^(8:ℕ)*a + (-1:ℂ)*x^(7:ℕ)*y*b + (-1:ℂ)*x^(7:ℕ)*a^(4:ℕ) + (3:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-3:ℂ)*x^(7:ℕ) + (-1:ℂ)*x^(6:ℕ)*y*a*b + (-1:ℂ)*x^(6:ℕ)*a^(5:ℕ) + (2:ℂ)*x^(6:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ) + x^(5:ℕ)*y*a^(4:ℕ)*b + (-3:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + x^(5:ℕ)*y*b + (-2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + (4:ℂ)*x^(5:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(5:ℕ) + x^(4:ℕ)*y^(3:ℕ)*a*b + (2:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(4:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*a^(3:ℕ) + x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(3:ℕ)*a^(2:ℕ)*b + x^(3:ℕ)*y^(3:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(3:ℕ)*y^(2:ℕ) + (2:ℂ)*x^(3:ℕ)*y*a^(4:ℕ)*b + (-5:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + x^(3:ℕ)*y*b + x^(3:ℕ)*z*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*z + (2:ℂ)*x^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ) + x^(2:ℕ)*y^(2:ℕ)*a + x^(2:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(2:ℕ)*y*a*b + (-1:ℂ)*x*y*a^(2:ℕ)*b + (2:ℂ)*x*a^(2:ℕ) + (-2:ℂ)*x + (-1:ℂ)*a)) = (x^(6:ℕ)*a)*0 + ((-1:ℂ))*((x*a)*(x^(10:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(10:ℕ)*a + (-1:ℂ)*x^(9:ℕ)*y*a^(2:ℕ)*b + x^(9:ℕ)*y*b + x^(9:ℕ)*a^(4:ℕ) + (-2:ℂ)*x^(9:ℕ)*a^(2:ℕ) + x^(9:ℕ) + (-1:ℂ)*x^(8:ℕ)*y*a^(3:ℕ)*b + x^(8:ℕ)*y*a*b + x^(8:ℕ)*a + (-1:ℂ)*x^(7:ℕ)*y*a^(2:ℕ)*b + x^(7:ℕ)*y*b + x^(7:ℕ)*a^(4:ℕ) + (-3:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (4:ℂ)*x^(7:ℕ) + (-1:ℂ)*x^(6:ℕ)*y*a^(3:ℕ)*b + x^(6:ℕ)*y*a*b + x^(6:ℕ)*a^(5:ℕ) + (-2:ℂ)*x^(6:ℕ)*a^(3:ℕ) + (3:ℂ)*x^(6:ℕ)*a + x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a^(4:ℕ)*b + (2:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*b + (2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + (-4:ℂ)*x^(5:ℕ)*a^(2:ℕ) + (3:ℂ)*x^(5:ℕ) + (-2:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(4:ℕ)*y*a*b + x^(4:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(4:ℕ)*a + x^(3:ℕ)*y^(3:ℕ)*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*y^(3:ℕ)*b + (2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(3:ℕ)*y^(2:ℕ) + (-2:ℂ)*x^(3:ℕ)*y*a^(4:ℕ)*b + (5:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ)*z*a^(2:ℕ) + x^(3:ℕ)*z + (-2:ℂ)*x^(3:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(2:ℕ)*y*a*b + x*y*a^(2:ℕ)*b + (-2:ℂ)*x*a^(2:ℕ) + (2:ℂ)*x + a)) + (x^(4:ℕ)*y*a*b)*((x*a)*((-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + y^(2:ℕ))) + (x^(3:ℕ))*((x^(3:ℕ)*a)*(x^(2:ℕ) + x*a + (1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3888_21 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ))*0 + (x^(4:ℕ)*y*a*b)*0 + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3888_42 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(9:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(9:ℕ)*a^(4:ℕ) + x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ)*y*a*b + (-1:ℂ)*x^(8:ℕ)*a^(5:ℕ) + (2:ℂ)*x^(8:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(8:ℕ)*a + x^(7:ℕ)*y*a^(4:ℕ)*b + (-2:ℂ)*x^(7:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + x^(6:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(6:ℕ)*y*a*b + (-1:ℂ)*x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a^(4:ℕ)*b + x^(5:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*b + x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (2:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a + (2:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(4:ℕ)*y*a*b + (-2:ℂ)*x^(4:ℕ)*a^(5:ℕ) + (6:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (-4:ℂ)*x^(4:ℕ)*a + x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*b^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ) + x^(3:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ)*a^(4:ℕ) + (2:ℂ)*x^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*a*b + x^(2:ℕ)*a + (2:ℂ)*x*a^(2:ℕ) + (-2:ℂ)*x + (-1:ℂ)*a)) = (x^(6:ℕ)*a)*0 + ((-1:ℂ))*(((1:ℂ))*(x^(9:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ)*y*a^(3:ℕ)*b + x^(8:ℕ)*y*a*b + x^(8:ℕ)*a^(5:ℕ) + (-2:ℂ)*x^(8:ℕ)*a^(3:ℕ) + x^(8:ℕ)*a + (-1:ℂ)*x^(7:ℕ)*y*a^(4:ℕ)*b + x^(7:ℕ)*y*a^(2:ℕ)*b + x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*y*a^(3:ℕ)*b + x^(6:ℕ)*y*a*b + x^(6:ℕ)*a + x^(5:ℕ)*y*a^(4:ℕ)*b + (-2:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + x^(5:ℕ)*y*b + x^(5:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a + (-2:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(4:ℕ)*y*a*b + (2:ℂ)*x^(4:ℕ)*a^(5:ℕ) + (-6:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (5:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(3:ℕ)*y*b + x^(3:ℕ)*a^(4:ℕ) + (-2:ℂ)*x^(3:ℕ)*a^(2:ℕ) + x^(3:ℕ) + x^(2:ℕ)*y*a*b + (-1:ℂ)*x^(2:ℕ)*a + (-2:ℂ)*x*a^(2:ℕ) + (2:ℂ)*x + a)) + (x^(4:ℕ)*y*a*b)*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (-1:ℂ)*x*a + (-1:ℂ)*y*b)) + (x^(3:ℕ))*(((1:ℂ))*(x^(3:ℕ)*a + x^(2:ℕ)*a^(2:ℕ) + x*a + (1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) := by ring1

compact_certificate theorem combination0_3888_45 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*((y)*((-1:ℂ)*b)) + ((-1:ℂ))*0 + (x^(4:ℕ)*y*a*b)*0 + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3888_53 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + (x^(4:ℕ)*y*a*b)*0 + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3888_72 (x y z a b : ℂ) :
    ((1:ℂ))*((x)*((-1:ℂ)*x^(8:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(8:ℕ)*a^(4:ℕ) + x^(8:ℕ)*a^(2:ℕ) + x^(7:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(7:ℕ)*y*a*b + (-1:ℂ)*x^(6:ℕ)*y*b + (-1:ℂ)*x^(6:ℕ)*a^(4:ℕ) + x^(6:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a + (2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + (-3:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y*a^(4:ℕ)*b + (4:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(4:ℕ)*y*b + x^(3:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(3:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(2:ℕ)*a^(4:ℕ) + (6:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(2:ℕ) + (2:ℂ)*x*a^(3:ℕ) + (-2:ℂ)*x*a + (-1:ℂ)*a^(2:ℕ))) = (x^(6:ℕ)*a)*0 + ((-1:ℂ))*((x)*(x^(8:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(8:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a^(3:ℕ)*b + x^(7:ℕ)*y*a*b + (-1:ℂ)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y*b + x^(6:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a + (-2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + (3:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ) + x^(4:ℕ)*y*a^(4:ℕ)*b + (-3:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(4:ℕ)*y*b + x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(2:ℕ)*a^(4:ℕ) + (-6:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(2:ℕ) + (-2:ℂ)*x*a^(3:ℕ) + (2:ℂ)*x*a + a^(2:ℕ))) + (x^(4:ℕ)*y*a*b)*((x)*((-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*b + (-1:ℂ)*y*a*b + a)) + (x^(3:ℕ))*((x)*(x^(2:ℕ)*a + x + a)) + ((-1:ℂ)*x^(6:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3888_90 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*0 + ((-1:ℂ))*0 + (x^(4:ℕ)*y*a*b)*((x*a)*((1:ℂ))) + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*(((1:ℂ))*((-1:ℂ)*x*a)) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3888_91 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*((x^(6:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + (x^(4:ℕ)*y*a*b)*0 + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3888_93 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*0 + ((-1:ℂ))*0 + (x^(4:ℕ)*y*a*b)*0 + (x^(3:ℕ))*((x^(3:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(4:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3890_0 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_102 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_103 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*((x^2*y^2)*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_108 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_109 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*((x^2*y^2)*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_12 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_13 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*((x^2*y^2)*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_18 (x y z a b : ℂ) :
    ((1))*((x*a)*((-1)*x^11*y*b + (-2)*x^11 + (-1)*x^10*y*a*b + (-1)*x^10*a^3 + (-2)*x^10*a + x^9*y*a^2*b + (-1)*x^9*y*b + (-1)*x^9*a^4 + x^9*a^2 + (-3)*x^9 + x^8*y*a^3*b + (-1)*x^8*y*a*b + (-2)*x^8*a + (-1)*x^7*a^4 + (-1)*x^7 + (-1)*x^6*y^2*a + x^6*y*a^3*b + (-2)*x^6*y*a*b + (-1)*x^6*a^5 + (-1)*x^6*a^3 + x^5*y^3*b + (-2)*x^5*y^2*a^2 + (2)*x^5*y^2 + x^5*y*a^4*b + (-2)*x^5*a^4 + x^5*a^2 + (-1)*x^4*y^2*a + (4)*x^4*y*a^3*b + (-4)*x^4*y*a*b + x^4*z*a + (-1)*x^4*a^3 + (4)*x^4*a + (-1)*x^3*y^3*a^2*b + (-2)*x^3*y^2*a^2 + (2)*x^3*y*a^4*b + (-3)*x^3*y*a^2*b + x^3*y*b + x^3*z*a^2 + (2)*x^3*a^2 + (-1)*x^3 + x^2*y^2*a + x^2*y*a^3*b + (-2)*x^2*y*a*b + (2)*x^2*a + (-1)*x*y*a^2*b + (2)*x*a^2 + (-2)*x + (-1)*a)) = (x^4*a)*(((1))*((1))) + ((-1))*((x*a)*(x^10*a^3 + (-1)*x^10*a + (-1)*x^9*y*a^2*b + x^9*y*b + x^9*a^4 + (-2)*x^9*a^2 + x^9 + (-1)*x^8*y*a^3*b + x^8*y*a*b + x^8*a + (-1)*x^7*y*a^2*b + x^7*y*b + x^7*a^4 + (-3)*x^7*a^2 + (4)*x^7 + (-1)*x^6*y*a^3*b + x^6*y*a*b + x^6*a^5 + (-2)*x^6*a^3 + (3)*x^6*a + x^5*y^2*a^2 + (-1)*x^5*y^2 + (-1)*x^5*y*a^4*b + (2)*x^5*y*a^2*b + (-1)*x^5*y*b + (2)*x^5*a^4 + (-4)*x^5*a^2 + (3)*x^5 + (-2)*x^4*y*a^3*b + (2)*x^4*y*a*b + x^4*a^3 + (-1)*x^4*a + x^3*y^3*a^2*b + (-1)*x^3*y^3*b + (2)*x^3*y^2*a^2 + (-2)*x^3*y^2 + (-2)*x^3*y*a^4*b + (5)*x^3*y*a^2*b + (-2)*x^3*y*b + (-1)*x^3*z*a^2 + x^3*z + (-2)*x^3*a^2 + (2)*x^3 + (-1)*x^2*y^2*a + (-1)*x^2*y*a^3*b + (2)*x^2*y*a*b + x*y*a^2*b + (-2)*x*a^2 + (2)*x + a)) + ((-1)*x^2)*((x*a)*((-1)*x^10*a + x^9*y*b + (-1)*x^9*a^2 + x^9 + x^8*y*a*b + x^7*y*b + (-1)*x^7*a^2 + (3)*x^7 + x^6*y*a*b + (-1)*x^6*a^3 + x^6*a + (-1)*x^5*y^2 + x^5*y*a^2*b + (-1)*x^5*y*b + (-1)*x^5*a^2 + x^5 + (2)*x^4*y*a*b + x^4*a^3 + (-2)*x^4*a + (-1)*x^3*y^3*b + (-2)*x^3*y^2 + x^3*y*a^2*b + (-1)*x^3*y*b + x^3*z + x^3*a^2 + x^3 + (-1)*x^2*y*a^3*b + (3)*x^2*y*a*b + (-1)*x*y*a^2*b + x*y*b + (2)*x + (-1)*a)) + ((-1)*x^2)*((x*a)*(x^10*a + x^9*a^2 + x^8*a + x^7*a^2 + x^6*a^3 + (2)*x^5*a^2 + (-1)*x^5 + (-1)*x^4*y^2*a + x^4*a^3 + (-1)*x^4*a + (-1)*x^3*y*a^2*b + x^3*a^2 + (-1)*x^2*y*a^3*b + x^2*y*a*b + (-1)*x*y*a^2*b + (-1)*a)) + ((-1)*x^3*y*b + (-1)*x^3)*((x*a)*((-1)*x^6 + (-1)*x^5*a + (-1)*x^4 + (-1)*x^3*a + (-1)*x^2*a^2 + (-1)*x*a + y^2)) + (x^3)*0 + ((-1)*x^5*a)*((a)*(x^6 + x^5*a + x^4 + x^3*a + x^2*a^2 + x*a)) + ((-1)*x^3)*((x*a)*((-1)*x^3*y*a*b + (-1)*x^2*y*a^2*b + x^2*y*b + (-1)*x^2 + (-1)*x*y*a*b + (-1)*x*a + (-2))) + ((-1)*x^4*a)*((x)*(x^3*y^2 + x^2*y^2*a + x^2*a + x*y^2 + x*a^2 + (-1)*x + a)) + ((-1)*x^4)*((x^2*a)*((-1)*x^4 + (-1)*x^3*a + x^2*y*b + (-1)*x^2 + x*y*a*b + y*b)) + ((-1)*x^7)*((x^3*a)*(x^2 + x*a + (1))) + (x^6*a)*(((1))*((-1)*x^3*a + (-1)*x^2*a^2 + (-1)*x*a)) + ((-1)*x^5*a)*((x)*((-1)*x^2 + (-1)*x*a + (-1))) + (x^4*y^2*a)*((x)*((-1)*x^2*a + (-1)*x*a^2 + x + (-1)*a)) + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*(((1))*(x^2*y^2 + (-1)*x*a + y^2 + (-1))) + ((-1)*x^4*a)*(((1))*((1))) + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*(((1))*((-1)*x^2 + (-1)*x*a + (-1))) + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*(((1))*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((-1))) + ((-1)*x^4*a)*(((1))*((-1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_19 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*((x^2*y^2)*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_24 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*(((1))*((1))) + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*(((1))*((-1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_25 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*((x^3*y^2*a)*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_28 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*0 + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*((y^2)*((1))) + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*(((1))*((1))) + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_30 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*((x*a)*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_31 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*((x^2*y^2*a)*((1))) + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_36 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*(((1))*((1))) + ((-2)*x^4*a)*0 + (x^4*z*a)*(((1))*((1))) + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_37 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*((x^2*y^2)*((1))) + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_42 (x y z a b : ℂ) :
    ((1))*(((1))*((-1)*x^10*y*a*b + (-2)*x^10*a + (-1)*x^9*y*a^2*b + (-1)*x^9*a^4 + (-1)*x^9*a^2 + x^8*y*a^3*b + (-1)*x^8*y*a*b + (-1)*x^8*a^5 + x^8*a^3 + (-3)*x^8*a + x^7*y*a^4*b + (-1)*x^7*y*b + (-1)*x^7*a^2 + (-2)*x^7 + (-1)*x^6*y^2*a*b^2 + x^6*y^2*a + x^6*y*a^3*b + (-3)*x^6*y*a*b + x^6*a^3 + (-3)*x^6*a + (-1)*x^5*y^2*a^2 + (-1)*x^5*y^2*b^2 + x^5*y^2 + (-1)*x^5*y*a^4*b + (2)*x^5*y*a^2*b + (-2)*x^5*y*b + (-2)*x^5*a^4 + (2)*x^5*a^2 + x^4*y^2*a^3*b^2 + (-1)*x^4*y^2*a^3 + (2)*x^4*y*a^3*b + (-2)*x^4*a^5 + (4)*x^4*a^3 + (-2)*x^4*a + x^3*y^2*a^2*b^2 + (-1)*x^3*y^2*a^2 + x^3*y*a^2*b + (-1)*x^3*y*b + (-1)*x^3*a^4 + x^3*a^2 + (-1)*x^3 + (-1)*x^2*y*a*b + (3)*x^2*a + (2)*x*a^2 + (-2)*x + (-1)*a)) = (x^4*a)*(((1))*((1))) + ((-1))*(((1))*(x^9*a^4 + (-1)*x^9*a^2 + (-1)*x^8*y*a^3*b + x^8*y*a*b + x^8*a^5 + (-2)*x^8*a^3 + x^8*a + (-1)*x^7*y*a^4*b + x^7*y*a^2*b + x^7*a^2 + (-1)*x^6*y*a^3*b + x^6*y*a*b + x^6*a + x^5*y*a^4*b + (-2)*x^5*y*a^2*b + x^5*y*b + x^5 + (-1)*x^4*y^2*a^3*b^2 + x^4*y^2*a^3 + x^4*y^2*a*b^2 + (-1)*x^4*y^2*a + (-2)*x^4*y*a^3*b + (2)*x^4*y*a*b + (2)*x^4*a^5 + (-6)*x^4*a^3 + (5)*x^4*a + (-1)*x^3*y^2*a^2*b^2 + x^3*y^2*a^2 + x^3*y^2*b^2 + (-1)*x^3*y^2 + (-1)*x^3*y*a^2*b + (2)*x^3*y*b + x^3*a^4 + (-2)*x^3*a^2 + x^3 + x^2*y*a*b + (-1)*x^2*a + (-2)*x*a^2 + (2)*x + a)) + ((-1)*x^2)*(((1))*((-1)*x^9*a^2 + x^8*y*a*b + (-1)*x^8*a^3 + x^8*a + x^7*y*a^2*b + x^6*y*a*b + x^6*a + (-1)*x^5*y*a^2*b + x^5*y*b + x^5 + x^4*y^2*a*b^2 + (-1)*x^4*y^2*a + (2)*x^4*y*a*b + (-2)*x^4*a^3 + (4)*x^4*a + x^3*y^2*b^2 + (-1)*x^3*y^2 + (2)*x^3*y*b + x^3*a^4 + (-3)*x^3*a^2 + x^3 + x^2*a^3 + (-2)*x^2*a + x + (-1)*a)) + ((-1)*x^2)*(((1))*(x^9*a^2 + x^8*a^3 + x^7*a^2 + x^6*a + x^5*y*a^2*b + x^5*a^2 + x^4*y*a*b + x^4*a^3 + (-1)*x^4*a + x^3*a^4 + (-1)*x^3*a^2 + x^2*a^3 + (-1)*x^2*a + x*a^2 + (-1)*x + (-1)*a)) + ((-1)*x^3*y*b + (-1)*x^3)*(((1))*((-1)*x^5*a + (-1)*x^4*a^2 + (-1)*x^3*a + (-1)*x^2 + (-1)*x*y*a*b + (-1)*x*a + (-1)*y*b)) + (x^3)*((y^2)*((-1)*x*a + (-1))) + ((-1)*x^5*a)*(((1))*(x^3*a^2 + x^2*a + x + a)) + ((-1)*x^3)*(((1))*((-1)*x*a + (-1))) + ((-1)*x^4*a)*((x*y^2)*(a)) + ((-1)*x^4)*(((1))*((-1)*x^3*a^2 + (-1)*x^2*a + x*a^2 + (-1)*x + a)) + ((-1)*x^7)*(((1))*(x^3*a + x^2*a^2 + x*a + (1))) + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*(((1))*(x*a + (1))) + ((-1)*x^3)*(((1))*((-1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_43 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*((x*y^2)*((1))) + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_46 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*0 + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*((x*y^2*a)*((1))) + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*((y^2)*((1))) + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_48 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_49 (x y z a b : ℂ) :
    ((1))*((x^6*y^2*a)*((1))) = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_54 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((1))) := by ring1

compact_certificate theorem combination0_3890_55 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*((x^2*y^2)*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_60 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_61 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*((x^2*y^2)*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_66 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*(((1))*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((-1))) + ((-1)*x^4*a)*(((1))*((-1))) + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_67 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*((x^2*y^2)*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_6 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((1))) + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_72 (x y z a b : ℂ) :
    ((1))*((x)*((-1)*x^9*y*a*b + (-2)*x^9*a + (-1)*x^8*y*b + (-1)*x^8*a^4 + x^8*a^2 + (-2)*x^8 + x^7*y*a^3*b + (-1)*x^7*y*a*b + (-3)*x^7*a + (-1)*x^6*y^2*b^2 + x^6*y^2 + x^6*y*a^2*b + (-2)*x^6*y*b + (-1)*x^6*a^4 + x^6*a^2 + (-1)*x^5*y^2*a*b^2 + x^5*y^2*a + x^5*a^3 + x^4*y^2*a^2*b^2 + (-1)*x^4*y^2*a^2 + (-1)*x^4*y*a^4*b + (3)*x^4*y*a^2*b + (-1)*x^4*y*b + (-1)*x^4*a^2 + (-1)*x^4 + x^3*y^2*a^3*b^2 + x^3*y*a^3*b + (-2)*x^3*y*a*b + (-3)*x^3*a^3 + (4)*x^3*a + (-1)*x^2*y*a^2*b + (-2)*x^2*a^4 + (7)*x^2*a^2 + (-2)*x^2 + (2)*x*a^3 + (-2)*x*a + (-1)*a^2)) = (x^4*a)*(((1))*((1))) + ((-1))*((x)*(x^8*a^4 + (-1)*x^8*a^2 + (-1)*x^7*y*a^3*b + x^7*y*a*b + (-1)*x^6*y*a^2*b + x^6*y*b + x^6*a^4 + (-1)*x^6*a^2 + x^6 + (-1)*x^5*y^2*a + (-2)*x^5*a^3 + (3)*x^5*a + (-1)*x^4*y^2*a^2*b^2 + x^4*y^2*a^2 + x^4*y^2*b^2 + (-1)*x^4*y^2 + x^4*y*a^4*b + (-3)*x^4*y*a^2*b + (2)*x^4*y*b + x^4 + (-1)*x^3*y^2*a^3*b^2 + x^3*y^2*a*b^2 + (-1)*x^3*y*a^3*b + (2)*x^3*y*a*b + x^3*a^3 + (-1)*x^3*a + x^2*y*a^2*b + (2)*x^2*a^4 + (-6)*x^2*a^2 + (2)*x^2 + (-2)*x*a^3 + (2)*x*a + a^2)) + ((-1)*x^2)*((x)*((-1)*x^8*a^2 + x^7*y*a*b + x^6*y*b + (-1)*x^6*a^2 + x^6 + (2)*x^5*a + x^4*y^2*b^2 + (-1)*x^4*y^2 + (-1)*x^4*y*a^2*b + (2)*x^4*y*b + x^4 + x^3*y^2*a*b^2 + x^3*y*a*b + (-1)*x^3*a + (-1)*x^2*a^2 + x^2 + x*a^3 + (-1)*x*a + (-1)*a^2)) + ((-1)*x^2)*((x^2)*(x^7*a^2 + x^6*a + x^5*a^2 + x^4*y*a*b + x^3*y*a^2*b + (-1)*x^3*a^2 + x^2*a^3 + (-1)*x^2*a + x*a^2 + (-1)*x + a^3 + (-2)*a)) + ((-1)*x^3*y*b + (-1)*x^3)*((x)*((-1)*x^4*a + (-1)*x^3 + (-1)*x^2*a + (-1)*x*y*b + (-1)*y*a*b + a)) + (x^3)*((x)*((-1)*x*y^2 + (-1)*y^2*a + a)) + ((-1)*x^5*a)*(((1))*(x^3 + x^2*a)) + ((-1)*x^3)*((x)*((-1)*x + (-1)*a)) + ((-1)*x^4*a)*0 + ((-1)*x^4)*(((1))*((-1)*x^3 + x*a^2 + a)) + ((-1)*x^7)*((x)*(x^2*a + x + a)) + (x^6*a)*(((1))*((1))) + ((-1)*x^5*a)*0 + (x^4*y^2*a)*(((1))*((1))) + ((-2)*x^3)*((x)*(x + a)) + ((-1)*x^3)*((x)*((-1)*x)) + ((-1)*x^4*a)*((x^2)*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((-1))) + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_73 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*((x^4*y^2*a)*((1))) + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_75 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*0 + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*((x^2)*((1))) + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*((x^2*y^2)*((1))) + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_78 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*0 + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*(((1))*((1))) + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*(z)) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_79 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*((x^4*y^2*a)*((1))) + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_7 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*((y^2)*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_84 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*((x*a)*((1))) + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((-1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_85 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*(((1))*((1))) + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_86 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*0 + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*((y^2*a)*((1))) + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*((y^2)*((-1)*a)) + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_90 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*((x*a)*((1))) + (x^3)*((x*a)*(y*b + (1))) + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*(((1))*((1))) + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((-1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_91 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*((x^6*y^2*a)*((1))) + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_93 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*0 + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*((x^3*a)*((1))) + (x^6*a)*(((1))*(x^4)) + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_96 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*(((1))*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*(((1))*((1))) + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_97 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*((x^2*y^2)*((1))) + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*((x^2*y^2)*((1))) + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

compact_certificate theorem combination0_3890_99 (x y z a b : ℂ) :
    ((1))*0 = (x^4*a)*0 + ((-1))*0 + ((-1)*x^2)*0 + ((-1)*x^2)*0 + ((-1)*x^3*y*b + (-1)*x^3)*0 + (x^3)*0 + ((-1)*x^5*a)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4)*0 + ((-1)*x^7)*0 + (x^6*a)*0 + ((-1)*x^5*a)*0 + (x^4*y^2*a)*0 + ((-2)*x^3)*0 + ((-1)*x^3)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^6*y^2*a)*0 + ((-1)*x^4*z*a + (-1)*x^4*a)*0 + ((-2)*x^4*a)*0 + (x^4*z*a)*0 + ((-3)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*((x^2)*((1))) + ((-1)*x^6*a)*(((1))*((-1))) + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 + ((-1)*x^4*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3895_106 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ))*0 + ((-1:ℂ)*x)*0 + (x^(5:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3895_18 (x y z a b : ℂ) :
    ((1:ℂ))*((x*a)*(x^(11:ℕ)*y*b + x^(11:ℕ)*a^(2:ℕ) + x^(11:ℕ) + x^(10:ℕ)*y*a*b + (2:ℂ)*x^(10:ℕ)*a^(3:ℕ) + x^(10:ℕ)*a + (-1:ℂ)*x^(9:ℕ)*y*a^(2:ℕ)*b + x^(9:ℕ)*y*b + x^(9:ℕ)*a^(4:ℕ) + (2:ℂ)*x^(9:ℕ) + (-1:ℂ)*x^(8:ℕ)*y*a^(3:ℕ)*b + x^(8:ℕ)*y*a*b + x^(8:ℕ)*a^(3:ℕ) + x^(8:ℕ)*a + (2:ℂ)*x^(7:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + x^(7:ℕ) + x^(6:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(6:ℕ)*y*a*b + x^(6:ℕ)*a^(5:ℕ) + (2:ℂ)*x^(6:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(3:ℕ)*b + x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a^(4:ℕ)*b + (2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a + (-4:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (3:ℂ)*x^(4:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*z*a + x^(4:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(4:ℕ)*a + x^(3:ℕ)*y^(3:ℕ)*a^(2:ℕ)*b + (2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(3:ℕ)*y*a^(4:ℕ)*b + (2:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*z*a^(2:ℕ) + (-2:ℂ)*x^(3:ℕ)*a^(2:ℕ) + x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y*a^(3:ℕ)*b + x^(2:ℕ)*y*a*b + (-2:ℂ)*x^(2:ℕ)*a + x*y*a^(2:ℕ)*b + (-2:ℂ)*x*a^(2:ℕ) + x + a)) = (x^(4:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*((x*a)*((-1:ℂ)*x^(11:ℕ)*y*b + (-2:ℂ)*x^(11:ℕ) + (-1:ℂ)*x^(10:ℕ)*y*a*b + (-1:ℂ)*x^(10:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(10:ℕ)*a + x^(9:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(9:ℕ)*y*b + (-1:ℂ)*x^(9:ℕ)*a^(4:ℕ) + x^(9:ℕ)*a^(2:ℕ) + (-3:ℂ)*x^(9:ℕ) + x^(8:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(8:ℕ)*y*a*b + (-2:ℂ)*x^(8:ℕ)*a + (-1:ℂ)*x^(7:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(7:ℕ) + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a + x^(6:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(6:ℕ)*y*a*b + (-1:ℂ)*x^(6:ℕ)*a^(5:ℕ) + (-1:ℂ)*x^(6:ℕ)*a^(3:ℕ) + x^(5:ℕ)*y^(3:ℕ)*b + (-2:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(5:ℕ)*y^(2:ℕ) + x^(5:ℕ)*y*a^(4:ℕ)*b + (-2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a + (4:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (-4:ℂ)*x^(4:ℕ)*y*a*b + x^(4:ℕ)*z*a + (-1:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (4:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(3:ℕ)*a^(2:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(3:ℕ)*y*a^(4:ℕ)*b + (-3:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + x^(3:ℕ)*y*b + x^(3:ℕ)*z*a^(2:ℕ) + (2:ℂ)*x^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ) + x^(2:ℕ)*y^(2:ℕ)*a + x^(2:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(2:ℕ)*y*a*b + (2:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*a^(2:ℕ)*b + (2:ℂ)*x*a^(2:ℕ) + (-2:ℂ)*x + (-1:ℂ)*a)) + ((-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ))*((x*a)*((-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + y^(2:ℕ))) + ((-1:ℂ)*x)*((x*a)*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(2:ℕ)*y*b + x*y*a*b + (1:ℂ))) + (x^(5:ℕ)*a^(2:ℕ))*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3895_24 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ))*0 + ((-1:ℂ)*x)*0 + (x^(5:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) := by ring1

compact_certificate theorem combination0_3895_42 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*(x^(10:ℕ)*y*a*b + x^(10:ℕ)*a^(3:ℕ) + x^(10:ℕ)*a + x^(9:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(9:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(8:ℕ)*y*a^(3:ℕ)*b + x^(8:ℕ)*y*a*b + x^(8:ℕ)*a^(5:ℕ) + (2:ℂ)*x^(8:ℕ)*a + (-1:ℂ)*x^(7:ℕ)*y*a^(4:ℕ)*b + x^(7:ℕ)*y*b + (2:ℂ)*x^(7:ℕ)*a^(2:ℕ) + x^(7:ℕ) + x^(6:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a + (2:ℂ)*x^(6:ℕ)*y*a*b + (2:ℂ)*x^(6:ℕ)*a + x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ) + x^(5:ℕ)*y*a^(4:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + x^(5:ℕ)*y*b + (2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + (-2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(4:ℕ)*a^(5:ℕ) + (-3:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + x^(3:ℕ)*y*b + x^(3:ℕ)*a^(4:ℕ) + x^(3:ℕ) + x^(2:ℕ)*y*a*b + (-3:ℂ)*x^(2:ℕ)*a + (-2:ℂ)*x*a^(2:ℕ) + x + a)) = (x^(4:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(10:ℕ)*y*a*b + (-2:ℂ)*x^(10:ℕ)*a + (-1:ℂ)*x^(9:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(9:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + x^(8:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(8:ℕ)*y*a*b + (-1:ℂ)*x^(8:ℕ)*a^(5:ℕ) + x^(8:ℕ)*a^(3:ℕ) + (-3:ℂ)*x^(8:ℕ)*a + x^(7:ℕ)*y*a^(4:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*y*b + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(7:ℕ) + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ)*a + x^(6:ℕ)*y*a^(3:ℕ)*b + (-3:ℂ)*x^(6:ℕ)*y*a*b + x^(6:ℕ)*a^(3:ℕ) + (-3:ℂ)*x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*b^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a^(4:ℕ)*b + (2:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(5:ℕ)*y*b + (-2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + (2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(4:ℕ)*a^(5:ℕ) + (4:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(4:ℕ)*a + x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ)*a^(4:ℕ) + x^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*a*b + (3:ℂ)*x^(2:ℕ)*a + (2:ℂ)*x*a^(2:ℕ) + (-2:ℂ)*x + (-1:ℂ)*a)) + ((-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ))*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (-1:ℂ)*x*a + (-1:ℂ)*y*b)) + ((-1:ℂ)*x)*(((1:ℂ))*((-1:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (1:ℂ))) + (x^(5:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3895_49 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*((x^(6:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ))*0 + ((-1:ℂ)*x)*0 + (x^(5:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3895_72 (x y z a b : ℂ) :
    ((1:ℂ))*((x)*(x^(9:ℕ)*y*a*b + x^(9:ℕ)*a^(3:ℕ) + x^(9:ℕ)*a + x^(8:ℕ)*y*b + x^(8:ℕ)*a^(4:ℕ) + x^(8:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a^(3:ℕ)*b + x^(7:ℕ)*y*a*b + x^(7:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(7:ℕ)*a + x^(6:ℕ)*y^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ) + x^(6:ℕ)*y*b + x^(6:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a + x^(5:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*a*b + (-2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y*a^(4:ℕ)*b + (-3:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y*b + x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(3:ℕ)*y*a*b + (3:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (-3:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(2:ℕ)*a^(4:ℕ) + (-6:ℂ)*x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ) + (-2:ℂ)*x*a^(3:ℕ) + x*a + a^(2:ℕ))) = (x^(4:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*((x)*((-1:ℂ)*x^(9:ℕ)*y*a*b + (-2:ℂ)*x^(9:ℕ)*a + (-1:ℂ)*x^(8:ℕ)*y*b + (-1:ℂ)*x^(8:ℕ)*a^(4:ℕ) + x^(8:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(8:ℕ) + x^(7:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*y*a*b + (-3:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*b^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ) + x^(6:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(6:ℕ)*y*b + (-1:ℂ)*x^(6:ℕ)*a^(4:ℕ) + x^(6:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a + x^(5:ℕ)*a^(3:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y*a^(4:ℕ)*b + (3:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(4:ℕ)*y*b + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + x^(3:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y*a*b + (-3:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (4:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(2:ℕ)*a^(4:ℕ) + (7:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(2:ℕ) + (2:ℂ)*x*a^(3:ℕ) + (-2:ℂ)*x*a + (-1:ℂ)*a^(2:ℕ))) + ((-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ))*((x)*((-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*b + (-1:ℂ)*y*a*b + a)) + ((-1:ℂ)*x)*((x)*((-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*a^(2:ℕ) + x + a)) + (x^(5:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3895_82 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ))*0 + ((-1:ℂ)*x)*((x^(3:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + (x^(5:ℕ)*a^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3895_90 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x)*0 + (x^(5:ℕ)*a^(2:ℕ))*(((1:ℂ))*(x*a)) + ((-1:ℂ)*x^(6:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3895_98 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(4:ℕ)*y^(2:ℕ)*a)*((x)*((-1:ℂ)*a)) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ))*0 + ((-1:ℂ)*x)*0 + (x^(5:ℕ)*a^(2:ℕ))*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3896_11 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(5:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ))*0 + (x^(4:ℕ)*y*a*b)*0 + (x^(5:ℕ)*y^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3896_18 (x y z a b : ℂ) :
    ((1:ℂ))*((x*a)*((2:ℂ)*x^(11:ℕ)*y*b + (2:ℂ)*x^(11:ℕ) + (2:ℂ)*x^(10:ℕ)*y*a*b + x^(10:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(10:ℕ)*a + (-1:ℂ)*x^(9:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(9:ℕ)*y*b + x^(9:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + (4:ℂ)*x^(9:ℕ) + (-1:ℂ)*x^(8:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(8:ℕ)*y*a*b + (3:ℂ)*x^(8:ℕ)*a + x^(7:ℕ)*y*a^(2:ℕ)*b + x^(7:ℕ)*a^(4:ℕ) + (2:ℂ)*x^(7:ℕ) + x^(6:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y*a^(3:ℕ)*b + (3:ℂ)*x^(6:ℕ)*y*a*b + x^(6:ℕ)*a^(5:ℕ) + x^(6:ℕ)*a^(3:ℕ) + x^(6:ℕ)*a + (-2:ℂ)*x^(5:ℕ)*y^(3:ℕ)*b + (2:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(5:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a^(4:ℕ)*b + (2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a + (-4:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (5:ℂ)*x^(4:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*z*a + x^(4:ℕ)*a^(3:ℕ) + (-3:ℂ)*x^(4:ℕ)*a + x^(3:ℕ)*y^(3:ℕ)*a^(2:ℕ)*b + (2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ) + (-2:ℂ)*x^(3:ℕ)*y*a^(4:ℕ)*b + (3:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*z*a^(2:ℕ) + (-2:ℂ)*x^(3:ℕ)*a^(2:ℕ) + x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(2:ℕ)*y*a*b + (-2:ℂ)*x^(2:ℕ)*a + x*y*a^(2:ℕ)*b + (-2:ℂ)*x*a^(2:ℕ) + (2:ℂ)*x + a)) = (x^(6:ℕ)*a)*0 + ((-1:ℂ))*((x*a)*((-1:ℂ)*x^(11:ℕ)*y*b + (-2:ℂ)*x^(11:ℕ) + (-1:ℂ)*x^(10:ℕ)*y*a*b + (-1:ℂ)*x^(10:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(10:ℕ)*a + x^(9:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(9:ℕ)*y*b + (-1:ℂ)*x^(9:ℕ)*a^(4:ℕ) + x^(9:ℕ)*a^(2:ℕ) + (-3:ℂ)*x^(9:ℕ) + x^(8:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(8:ℕ)*y*a*b + (-2:ℂ)*x^(8:ℕ)*a + (-1:ℂ)*x^(7:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(7:ℕ) + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a + x^(6:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(6:ℕ)*y*a*b + (-1:ℂ)*x^(6:ℕ)*a^(5:ℕ) + (-1:ℂ)*x^(6:ℕ)*a^(3:ℕ) + x^(5:ℕ)*y^(3:ℕ)*b + (-2:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(5:ℕ)*y^(2:ℕ) + x^(5:ℕ)*y*a^(4:ℕ)*b + (-2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a + (4:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (-4:ℂ)*x^(4:ℕ)*y*a*b + x^(4:ℕ)*z*a + (-1:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (4:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(3:ℕ)*a^(2:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(3:ℕ)*y*a^(4:ℕ)*b + (-3:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + x^(3:ℕ)*y*b + x^(3:ℕ)*z*a^(2:ℕ) + (2:ℂ)*x^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ) + x^(2:ℕ)*y^(2:ℕ)*a + x^(2:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(2:ℕ)*y*a*b + (2:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*a^(2:ℕ)*b + (2:ℂ)*x*a^(2:ℕ) + (-2:ℂ)*x + (-1:ℂ)*a)) + ((-1:ℂ)*x^(5:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ))*((x*a)*((-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + y^(2:ℕ))) + (x^(4:ℕ)*y*a*b)*(((1:ℂ))*(x*a + (1:ℂ))) + (x^(5:ℕ)*y^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3896_30 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x^(5:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ))*0 + (x^(4:ℕ)*y*a*b)*0 + (x^(5:ℕ)*y^(2:ℕ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3896_33 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*((y)*((-1:ℂ)*b)) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(5:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ))*0 + (x^(4:ℕ)*y*a*b)*((x^(2:ℕ))*((1:ℂ))) + (x^(5:ℕ)*y^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3896_42 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*((2:ℂ)*x^(10:ℕ)*y*a*b + (2:ℂ)*x^(10:ℕ)*a + (2:ℂ)*x^(9:ℕ)*y*a^(2:ℕ)*b + x^(9:ℕ)*a^(4:ℕ) + x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(8:ℕ)*y*a*b + x^(8:ℕ)*a^(5:ℕ) + (-1:ℂ)*x^(8:ℕ)*a^(3:ℕ) + (4:ℂ)*x^(8:ℕ)*a + (-1:ℂ)*x^(7:ℕ)*y*a^(4:ℕ)*b + (2:ℂ)*x^(7:ℕ)*y*b + (2:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(7:ℕ) + (2:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y*a^(3:ℕ)*b + (4:ℂ)*x^(6:ℕ)*y*a*b + (-1:ℂ)*x^(6:ℕ)*a^(3:ℕ) + (4:ℂ)*x^(6:ℕ)*a + x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(5:ℕ)*y^(2:ℕ)*b^(2:ℕ) + (-2:ℂ)*x^(5:ℕ)*y^(2:ℕ) + x^(5:ℕ)*y*a^(4:ℕ)*b + (-2:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(5:ℕ)*y*b + (2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + (-2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + x^(4:ℕ)*y*a*b + (2:ℂ)*x^(4:ℕ)*a^(5:ℕ) + (-4:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (3:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(3:ℕ)*y*b + x^(3:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a^(2:ℕ) + x^(3:ℕ) + x^(2:ℕ)*y*a*b + (-3:ℂ)*x^(2:ℕ)*a + (-2:ℂ)*x*a^(2:ℕ) + (2:ℂ)*x + a)) = (x^(6:ℕ)*a)*0 + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(10:ℕ)*y*a*b + (-2:ℂ)*x^(10:ℕ)*a + (-1:ℂ)*x^(9:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(9:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + x^(8:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(8:ℕ)*y*a*b + (-1:ℂ)*x^(8:ℕ)*a^(5:ℕ) + x^(8:ℕ)*a^(3:ℕ) + (-3:ℂ)*x^(8:ℕ)*a + x^(7:ℕ)*y*a^(4:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*y*b + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(7:ℕ) + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ)*a + x^(6:ℕ)*y*a^(3:ℕ)*b + (-3:ℂ)*x^(6:ℕ)*y*a*b + x^(6:ℕ)*a^(3:ℕ) + (-3:ℂ)*x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*b^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a^(4:ℕ)*b + (2:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(5:ℕ)*y*b + (-2:ℂ)*x^(5:ℕ)*a^(4:ℕ) + (2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(4:ℕ)*a^(5:ℕ) + (4:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(4:ℕ)*a + x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ)*a^(4:ℕ) + x^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*a*b + (3:ℂ)*x^(2:ℕ)*a + (2:ℂ)*x*a^(2:ℕ) + (-2:ℂ)*x + (-1:ℂ)*a)) + ((-1:ℂ)*x^(5:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ))*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (-1:ℂ)*x*a + (-1:ℂ)*y*b)) + (x^(4:ℕ)*y*a*b)*0 + (x^(5:ℕ)*y^(2:ℕ))*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3896_49 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*((x^(6:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ))*0 + (x^(4:ℕ)*y*a*b)*0 + (x^(5:ℕ)*y^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3896_72 (x y z a b : ℂ) :
    ((1:ℂ))*((x)*((2:ℂ)*x^(9:ℕ)*y*a*b + (2:ℂ)*x^(9:ℕ)*a + (2:ℂ)*x^(8:ℕ)*y*b + x^(8:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(8:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(8:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(7:ℕ)*y*a*b + (4:ℂ)*x^(7:ℕ)*a + (2:ℂ)*x^(6:ℕ)*y^(2:ℕ)*b^(2:ℕ) + (-2:ℂ)*x^(6:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(6:ℕ)*y*b + x^(6:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ) + (2:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a*b + (-1:ℂ)*x^(5:ℕ)*a^(3:ℕ) + x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y*a^(4:ℕ)*b + (-3:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(4:ℕ)*y*b + x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y*a^(3:ℕ)*b + (3:ℂ)*x^(3:ℕ)*y*a*b + (3:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (-4:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(2:ℕ)*a^(4:ℕ) + (-7:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(2:ℕ) + (-2:ℂ)*x*a^(3:ℕ) + (2:ℂ)*x*a + a^(2:ℕ))) = (x^(6:ℕ)*a)*0 + ((-1:ℂ))*((x)*((-1:ℂ)*x^(9:ℕ)*y*a*b + (-2:ℂ)*x^(9:ℕ)*a + (-1:ℂ)*x^(8:ℕ)*y*b + (-1:ℂ)*x^(8:ℕ)*a^(4:ℕ) + x^(8:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(8:ℕ) + x^(7:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*y*a*b + (-3:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*b^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ) + x^(6:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(6:ℕ)*y*b + (-1:ℂ)*x^(6:ℕ)*a^(4:ℕ) + x^(6:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a + x^(5:ℕ)*a^(3:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y*a^(4:ℕ)*b + (3:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(4:ℕ)*y*b + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a^(3:ℕ)*b^(2:ℕ) + x^(3:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y*a*b + (-3:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (4:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(2:ℕ)*a^(4:ℕ) + (7:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(2:ℕ) + (2:ℂ)*x*a^(3:ℕ) + (-2:ℂ)*x*a + (-1:ℂ)*a^(2:ℕ))) + ((-1:ℂ)*x^(5:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ))*((x)*((-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*b + (-1:ℂ)*y*a*b + a)) + (x^(4:ℕ)*y*a*b)*0 + (x^(5:ℕ)*y^(2:ℕ))*((x)*((-1:ℂ)*x)) + ((-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3896_87 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(5:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ))*0 + (x^(4:ℕ)*y*a*b)*0 + (x^(5:ℕ)*y^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3896_90 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ)*x^(5:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ))*((x*a)*((1:ℂ))) + (x^(4:ℕ)*y*a*b)*((x^(2:ℕ))*((1:ℂ))) + (x^(5:ℕ)*y^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) := by ring1

compact_certificate theorem combination0_3896_99 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(6:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ)*x^(5:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ))*0 + (x^(4:ℕ)*y*a*b)*0 + (x^(5:ℕ)*y^(2:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3898_18 (x y z a b : ℂ) :
    ((1:ℂ))*((x*a)*(x^(11:ℕ)*a + (2:ℂ)*x^(10:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(9:ℕ)*y*a*b + x^(9:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a*b + (2:ℂ)*x^(7:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(7:ℕ)*a + x^(6:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y*b + x^(6:ℕ)*a^(4:ℕ) + x^(6:ℕ)*a^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(3:ℕ)*b + x^(5:ℕ)*a^(3:ℕ) + x^(5:ℕ)*a + x^(4:ℕ)*y^(2:ℕ) + (-3:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y*b + (-1:ℂ)*x^(4:ℕ)*z + (-1:ℂ)*x^(4:ℕ) + x^(3:ℕ)*y^(3:ℕ)*a*b + (2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*z*a + (-2:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*b + (-2:ℂ)*x^(2:ℕ) + x*y*a*b + (-1:ℂ)*x*a + (1:ℂ))) = (x^(3:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*((x*a)*((-1:ℂ)*x^(11:ℕ)*a + (-2:ℂ)*x^(10:ℕ)*a^(2:ℕ) + x^(9:ℕ)*y*a*b + (-1:ℂ)*x^(9:ℕ)*a^(3:ℕ) + x^(8:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(8:ℕ)*a^(2:ℕ) + x^(8:ℕ) + x^(7:ℕ)*y*a*b + (-2:ℂ)*x^(7:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ) + x^(6:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(6:ℕ)*y*b + (-1:ℂ)*x^(6:ℕ)*a^(4:ℕ) + (-2:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a + x^(5:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ) + (4:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(4:ℕ)*y*b + x^(4:ℕ)*z + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(3:ℕ)*a*b + (-2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a + (2:ℂ)*x^(3:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*z*a + (2:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (2:ℂ)*x*a + (-1:ℂ))) + (x*a)*((x*a)*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y*a^(2:ℕ)*b + x*y*a*b + (1:ℂ))) + (x^(2:ℕ))*((x^(3:ℕ)*a)*(x^(2:ℕ) + x*a + (1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*((y)*(x^(2:ℕ)*b + x*a*b + b)) := by ring1

compact_certificate theorem combination0_3898_26 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ))*0 + (x*a)*0 + (x^(2:ℕ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3898_35 (x y z a b : ℂ) :
    ((1:ℂ))*((x^(5:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) = (x^(3:ℕ)*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + (x*a)*0 + (x^(2:ℕ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3898_42 (x y z a b : ℂ) :
    ((1:ℂ))*(((1:ℂ))*(x^(10:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(9:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(9:ℕ)*a + (-1:ℂ)*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a^(3:ℕ)*b + x^(7:ℕ)*a + x^(5:ℕ)*y^(2:ℕ)*a + x^(5:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*a*b + x^(5:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(4:ℕ)*y*b + x^(4:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y*a*b + (2:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y*b + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a + (1:ℂ))) = (x^(3:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(10:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(9:ℕ)*a^(3:ℕ) + x^(9:ℕ)*a + x^(8:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(8:ℕ)*a^(4:ℕ) + x^(7:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(3:ℕ)*b + x^(5:ℕ)*y*a*b + (-2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + (2:ℂ)*x^(5:ℕ)*a + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y*b + (-2:ℂ)*x^(4:ℕ)*a^(4:ℕ) + (2:ℂ)*x^(4:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a + x^(3:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y*b + (2:ℂ)*x^(2:ℕ) + (2:ℂ)*x*a + (-1:ℂ))) + (x*a)*(((1:ℂ))*((-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + (1:ℂ))) + (x^(2:ℕ))*(((1:ℂ))*(x^(3:ℕ)*a + x^(2:ℕ)*a^(2:ℕ) + x*a + (1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3898_70 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*y^(2:ℕ)*a)*((x)*((-1:ℂ)*a)) + ((-1:ℂ))*0 + (x*a)*((x^(3:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + (x^(2:ℕ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3898_72 (x y z a b : ℂ) :
    ((1:ℂ))*((x)*(x^(9:ℕ)*a^(2:ℕ) + x^(8:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a^(2:ℕ)*b + x^(7:ℕ)*a^(2:ℕ) + x^(6:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(6:ℕ)*a + x^(5:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*b + (-2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y*a^(3:ℕ)*b + (-3:ℂ)*x^(4:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (3:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + x^(3:ℕ)*y*b + (2:ℂ)*x^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ) + x^(2:ℕ)*y*a*b + x^(2:ℕ)*a^(3:ℕ) + (-3:ℂ)*x^(2:ℕ)*a + (-2:ℂ)*x*a^(2:ℕ) + x + a)) = (x^(3:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*((x)*((-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ)*a^(3:ℕ) + x^(7:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*a^(3:ℕ) + x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + x^(5:ℕ)*y*b + (2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*y*a^(3:ℕ)*b + (3:ℂ)*x^(4:ℕ)*y*a*b + (-2:ℂ)*x^(4:ℕ)*a + x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(3:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*y*b + (-3:ℂ)*x^(3:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*a*b + (-2:ℂ)*x^(2:ℕ)*a^(3:ℕ) + (5:ℂ)*x^(2:ℕ)*a + (2:ℂ)*x*a^(2:ℕ) + (-1:ℂ)*x + (-1:ℂ)*a)) + (x*a)*((x^(2:ℕ))*((-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + (-1:ℂ)*a^(2:ℕ) + (1:ℂ))) + (x^(2:ℕ))*((x)*(x^(2:ℕ)*a + x + a)) + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3898_92 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*((x^(5:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + (x*a)*0 + (x^(2:ℕ))*0 + ((-1:ℂ)*x^(3:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3898_93 (x y z a b : ℂ) :
    ((1:ℂ))*0 = (x^(3:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + (x*a)*0 + (x^(2:ℕ))*((x^(3:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x^(3:ℕ)*a)*(((1:ℂ))*(x^(2:ℕ))) := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3906_0 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_101 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_102 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_104 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_107 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_108 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_11 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_12 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_17 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_18 (x y z a b : ℂ) :
    (x^(3:ℕ))*((x*a)*((-1:ℂ)*x^(10:ℕ)*a + (-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ)*a + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(3:ℕ) + x^(4:ℕ)*a + x^(3:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*a^(2:ℕ) + x^(2:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(2:ℕ)*y*a*b + x*y^(2:ℕ) + x*y*a^(2:ℕ)*b + x + a)) = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*((x*a)*(x^(11:ℕ)*a + (2:ℂ)*x^(10:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(9:ℕ)*y*a*b + x^(9:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a*b + (2:ℂ)*x^(7:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(7:ℕ)*a + x^(6:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y*b + x^(6:ℕ)*a^(4:ℕ) + x^(6:ℕ)*a^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(3:ℕ)*b + x^(5:ℕ)*a^(3:ℕ) + x^(5:ℕ)*a + x^(4:ℕ)*y^(2:ℕ) + (-3:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y*b + (-1:ℂ)*x^(4:ℕ)*z + (-1:ℂ)*x^(4:ℕ) + x^(3:ℕ)*y^(3:ℕ)*a*b + (2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*z*a + (-2:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*b + (-2:ℂ)*x^(2:ℕ) + x*y*a*b + (-1:ℂ)*x*a + (1:ℂ))) + ((-1:ℂ))*((x*a)*(x^(11:ℕ)*y*a*b + (2:ℂ)*x^(11:ℕ)*a + x^(10:ℕ)*y*a^(2:ℕ)*b + (3:ℂ)*x^(10:ℕ)*a^(2:ℕ) + x^(9:ℕ)*a^(3:ℕ) + x^(9:ℕ)*a + (2:ℂ)*x^(8:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(8:ℕ) + x^(7:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(7:ℕ)*y*a*b + (3:ℂ)*x^(7:ℕ)*a^(3:ℕ) + (-3:ℂ)*x^(7:ℕ)*a + x^(6:ℕ)*y^(2:ℕ) + x^(6:ℕ)*y*b + x^(6:ℕ)*a^(4:ℕ) + (3:ℂ)*x^(6:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(3:ℕ)*a*b + (-1:ℂ)*x^(5:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + x^(4:ℕ)*y^(2:ℕ) + (-4:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(4:ℕ)*y*b + (-1:ℂ)*x^(4:ℕ)*z + x^(4:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(4:ℕ) + x^(3:ℕ)*y^(3:ℕ)*a*b + (2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a + (-2:ℂ)*x^(3:ℕ)*y*a^(3:ℕ)*b + x^(3:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*z*a + (-2:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(2:ℕ) + x*y*a*b + (-2:ℂ)*x*a + (1:ℂ))) + ((1:ℂ))*((x*a)*(x^(10:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(9:ℕ)*y*a*b + x^(9:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(9:ℕ)*a + (-1:ℂ)*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a*b + x^(7:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(3:ℕ)*b + x^(5:ℕ)*y*a*b + (2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(5:ℕ)*a + (-2:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y^(3:ℕ)*a*b + (2:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a + (-2:ℂ)*x^(3:ℕ)*y*a^(3:ℕ)*b + (3:ℂ)*x^(3:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*z*a + (-2:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*a^(2:ℕ)*b + x*y*a*b + (-2:ℂ)*x*a + (1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*((x*a)*((-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + y^(2:ℕ))) + (x^(7:ℕ))*((a)*(x^(6:ℕ) + x^(5:ℕ)*a + x^(4:ℕ) + x^(3:ℕ)*a + x^(2:ℕ)*a^(2:ℕ) + x*a)) + ((-1:ℂ)*x^(4:ℕ))*((x*a)*(x^(3:ℕ)*y*a*b + x^(2:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(2:ℕ)*y*b + x^(2:ℕ) + x*y*a*b + x*a + (2:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*((x*a)*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y*a^(2:ℕ)*b + x*y*a*b + (1:ℂ))) + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*((x^(3:ℕ)*a)*(x^(2:ℕ) + x*a + (1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*((x)*((-1:ℂ)*x^(3:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y^(2:ℕ) + (-1:ℂ)*x*a^(2:ℕ) + x + (-1:ℂ)*a)) + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ)*x*a + (-1:ℂ)*y*b)) + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*(((1:ℂ))*((-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a)) + (x^(7:ℕ)*a)*((y)*(x^(2:ℕ)*b + x*a*b + b)) + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ)*x^(2:ℕ)*y^(2:ℕ) + x*a + (-1:ℂ)*y^(2:ℕ) + (1:ℂ))) + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*((x)*(x^(2:ℕ)*a + x*a^(2:ℕ) + (-1:ℂ)*x + a)) + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*((x)*(x^(2:ℕ) + x*a + (1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a + (-1:ℂ))) + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_23 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*((x^(7:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_24 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_26 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_28 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*((y^(2:ℕ))*((1:ℂ))) + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*((y^(2:ℕ))*((-1:ℂ)*a)) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_29 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_30 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_35 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*((x^(5:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_36 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*(z)) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_39 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_41 (x y z a b : ℂ) :
    (x^(3:ℕ))*((x^(4:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_42 (x y z a b : ℂ) :
    (x^(3:ℕ))*(((1:ℂ))*((-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*a^(4:ℕ) + x^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a^(3:ℕ) + x^(2:ℕ)*a + (2:ℂ)*x + a)) = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*(((1:ℂ))*(x^(10:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(9:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(9:ℕ)*a + (-1:ℂ)*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a^(3:ℕ)*b + x^(7:ℕ)*a + x^(5:ℕ)*y^(2:ℕ)*a + x^(5:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*a*b + x^(5:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(4:ℕ)*y*b + x^(4:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y*a*b + (2:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y*b + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a + (1:ℂ))) + ((-1:ℂ))*(((1:ℂ))*(x^(10:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(10:ℕ)*a^(2:ℕ) + x^(9:ℕ)*y*a^(3:ℕ)*b + (3:ℂ)*x^(9:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(9:ℕ)*a + x^(8:ℕ)*a^(4:ℕ) + x^(8:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(7:ℕ)*y*a^(3:ℕ)*b + x^(7:ℕ)*y*a*b + (2:ℂ)*x^(7:ℕ)*a + x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*a^(2:ℕ) + x^(5:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(5:ℕ)*y*a^(3:ℕ)*b + (2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(4:ℕ)*y*b + (2:ℂ)*x^(4:ℕ)*a^(4:ℕ) + (-2:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*a^(3:ℕ) + x^(3:ℕ)*a + x^(2:ℕ)*y*b + (-2:ℂ)*x^(2:ℕ) + (-2:ℂ)*x*a + (1:ℂ))) + ((1:ℂ))*(((1:ℂ))*(x^(9:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ)*a^(4:ℕ) + (-1:ℂ)*x^(8:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a^(3:ℕ)*b + x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(5:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(4:ℕ)*a^(4:ℕ) + (-4:ℂ)*x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*a^(3:ℕ) + x^(2:ℕ)*y*b + (-2:ℂ)*x*a + (1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (-1:ℂ)*x*a + (-1:ℂ)*y*b)) + (x^(7:ℕ))*(((1:ℂ))*(x^(3:ℕ)*a^(2:ℕ) + x^(2:ℕ)*a + x + a)) + ((-1:ℂ)*x^(4:ℕ))*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*(((1:ℂ))*((-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + (1:ℂ))) + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*(((1:ℂ))*(x^(3:ℕ)*a + x^(2:ℕ)*a^(2:ℕ) + x*a + (1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ))*(((1:ℂ))*(x*a + (1:ℂ))) + ((-2:ℂ)*x^(4:ℕ))*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_47 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_48 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_53 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_54 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3906_59 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_5 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_60 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_65 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_66 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_68 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*((x^(5:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_6 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_70 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*((x^(3:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((y^(2:ℕ))*((-1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_71 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*((x*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_72 (x y z a b : ℂ) :
    (x^(3:ℕ))*((x)*((-1:ℂ)*x^(8:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-2:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a^(3:ℕ) + (2:ℂ)*x*a + a^(2:ℕ))) = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*((x)*(x^(9:ℕ)*a^(2:ℕ) + x^(8:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a^(2:ℕ)*b + x^(7:ℕ)*a^(2:ℕ) + x^(6:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(6:ℕ)*a + x^(5:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*b + (-2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y*a^(3:ℕ)*b + (-3:ℂ)*x^(4:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (3:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + x^(3:ℕ)*y*b + (2:ℂ)*x^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ) + x^(2:ℕ)*y*a*b + x^(2:ℕ)*a^(3:ℕ) + (-3:ℂ)*x^(2:ℕ)*a + (-2:ℂ)*x*a^(2:ℕ) + x + a)) + ((-1:ℂ))*((x)*(x^(9:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(9:ℕ)*a^(2:ℕ) + x^(8:ℕ)*y*a*b + x^(8:ℕ)*a^(3:ℕ) + x^(8:ℕ)*a + (2:ℂ)*x^(7:ℕ)*a^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*y^(2:ℕ)*a + x^(6:ℕ)*y*a*b + x^(6:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(6:ℕ)*a + x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(5:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*b + (-2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y*a^(3:ℕ)*b + (-3:ℂ)*x^(4:ℕ)*y*a*b + (2:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + x^(3:ℕ)*y*b + (3:ℂ)*x^(3:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(3:ℕ) + x^(2:ℕ)*y*a*b + (2:ℂ)*x^(2:ℕ)*a^(3:ℕ) + (-5:ℂ)*x^(2:ℕ)*a + (-2:ℂ)*x*a^(2:ℕ) + x + a)) + ((1:ℂ))*((x)*(x^(8:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(6:ℕ)*y*a*b + x^(6:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*y*a^(3:ℕ)*b + (-2:ℂ)*x^(4:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + x^(3:ℕ)*y*b + x^(3:ℕ)*a^(2:ℕ) + x^(2:ℕ)*y*a*b + (2:ℂ)*x^(2:ℕ)*a^(3:ℕ) + (-4:ℂ)*x^(2:ℕ)*a + (-2:ℂ)*x*a^(2:ℕ) + x + a)) + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*((x)*((-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*b + (-1:ℂ)*y*a*b + a)) + (x^(7:ℕ))*(((1:ℂ))*(x^(3:ℕ) + x^(2:ℕ)*a)) + ((-1:ℂ)*x^(4:ℕ))*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*((x^(2:ℕ))*((-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + (-1:ℂ)*a^(2:ℕ) + (1:ℂ))) + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*((x)*(x^(2:ℕ)*a + x + a)) + ((-1:ℂ)*x^(5:ℕ)*a)*((x*y^(2:ℕ))*(a)) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*(((1:ℂ))*((1:ℂ))) + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*((x)*(x + a)) + ((-2:ℂ)*x^(4:ℕ))*((x)*((-1:ℂ)*x)) + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_77 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_78 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_83 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_84 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*((x*a)*((1:ℂ))) + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_86 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*((y^(2:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_89 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*((x^(3:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_90 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*((x*a)*((1:ℂ))) + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ))*((-1:ℂ)*a^(2:ℕ) + (1:ℂ))) + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_93 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*((x^(3:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*(((1:ℂ))*(x^(4:ℕ))) + (x^(7:ℕ)*a)*(((1:ℂ))*(x^(2:ℕ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_95 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*((x^(2:ℕ)*y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3906_96 (x y z a b : ℂ) :
    (x^(3:ℕ))*0 = (x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ))*0 + ((-1:ℂ))*0 + ((1:ℂ))*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ))*0 + (x^(7:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(2:ℕ))*0 + (x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ))*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(6:ℕ)*a^(2:ℕ))*0 + (x^(7:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*a)*0 + (x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ))*0 + ((-2:ℂ)*x^(4:ℕ))*0 + ((-1:ℂ)*x^(6:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(7:ℕ)*y^(2:ℕ)*a)*0 + (x^(5:ℕ)*z*a + x^(5:ℕ)*a)*0 + ((-2:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-3:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(5:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 + ((-1:ℂ)*x^(5:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3911_18 (x y z a b : ℂ) :
    (x)*((x*a)*((-1:ℂ)*y^(2:ℕ) + (-1:ℂ))) = (x^(2:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*((x*a)*((-1:ℂ)*x^(10:ℕ)*a + (-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ)*a + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(3:ℕ) + x^(4:ℕ)*a + x^(3:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*a^(2:ℕ) + x^(2:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(2:ℕ)*y*a*b + x*y^(2:ℕ) + x*y*a^(2:ℕ)*b + x + a)) + (x^(4:ℕ)*a)*((x*a)*((-1:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (-1:ℂ)*x*a + y^(2:ℕ))) + (a)*((x*a)*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*a + x^(2:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(2:ℕ)*y*b + x*y*a*b + (1:ℂ))) + (x)*((x^(3:ℕ)*a)*(x^(2:ℕ) + x*a + (1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3911_21 (x y z a b : ℂ) :
    (x)*0 = (x^(2:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + (x^(4:ℕ)*a)*0 + (a)*0 + (x)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*(((1:ℂ))*((-1:ℂ)*x^(2:ℕ))) := by ring1

compact_certificate theorem combination0_3911_41 (x y z a b : ℂ) :
    (x)*0 = (x^(2:ℕ)*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*((x^(4:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + (x^(4:ℕ)*a)*0 + (a)*0 + (x)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3911_42 (x y z a b : ℂ) :
    (x)*(((1:ℂ))*(x^(3:ℕ)*a + x^(2:ℕ) + (-1:ℂ))) = (x^(2:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*a^(4:ℕ) + x^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a^(3:ℕ) + x^(2:ℕ)*a + (2:ℂ)*x + a)) + (x^(4:ℕ)*a)*(((1:ℂ))*((-1:ℂ)*x^(5:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*y*a*b + (-1:ℂ)*x*a + (-1:ℂ)*y*b)) + (a)*(((1:ℂ))*((-1:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (1:ℂ))) + (x)*(((1:ℂ))*(x^(3:ℕ)*a + x^(2:ℕ)*a^(2:ℕ) + x*a + (1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3911_50 (x y z a b : ℂ) :
    (x)*0 = (x^(2:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ))*0 + (x^(4:ℕ)*a)*0 + (a)*0 + (x)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3911_72 (x y z a b : ℂ) :
    (x)*((x^(2:ℕ))*(x^(2:ℕ) + x*a + a^(2:ℕ) + (-1:ℂ))) = (x^(2:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*((x)*((-1:ℂ)*x^(8:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-2:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a^(3:ℕ) + (2:ℂ)*x*a + a^(2:ℕ))) + (x^(4:ℕ)*a)*((x)*((-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*y*b + (-1:ℂ)*y*a*b + a)) + (a)*((x)*((-1:ℂ)*x^(2:ℕ)*a + (-1:ℂ)*x*a^(2:ℕ) + x + a)) + (x)*((x)*(x^(2:ℕ)*a + x + a)) + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3911_82 (x y z a b : ℂ) :
    (x)*0 = (x^(2:ℕ)*y^(2:ℕ)*a)*((x)*((-1:ℂ)*a)) + ((-1:ℂ))*0 + (x^(4:ℕ)*a)*0 + (a)*((x^(3:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + (x)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3911_90 (x y z a b : ℂ) :
    (x)*0 = (x^(2:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + (x^(4:ℕ)*a)*((x*a)*((1:ℂ))) + (a)*0 + (x)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*(x*a)) + ((-1:ℂ)*x^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3911_93 (x y z a b : ℂ) :
    (x)*0 = (x^(2:ℕ)*y^(2:ℕ)*a)*0 + ((-1:ℂ))*0 + (x^(4:ℕ)*a)*0 + (a)*0 + (x)*((x^(3:ℕ)*a)*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3911_98 (x y z a b : ℂ) :
    (x)*0 = (x^(2:ℕ)*y^(2:ℕ)*a)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + (x^(4:ℕ)*a)*0 + (a)*0 + (x)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + ((-1:ℂ)*x^(4:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(2:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelNineteenPoleLeading

compact_certificate theorem combination0_3912_18 (x y z a b : ℂ) :
    (x)*((x*a)*((2:ℂ)*x^(9:ℕ)*a + (-1:ℂ)*x^(8:ℕ)*y*b + (2:ℂ)*x^(8:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a*b + x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y*b + (2:ℂ)*x^(6:ℕ)*a^(2:ℕ) + (-3:ℂ)*x^(6:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a*b + (2:ℂ)*x^(5:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(5:ℕ)*a + x^(4:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y*b + (3:ℂ)*x^(4:ℕ)*a^(2:ℕ) + (-2:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a + (-2:ℂ)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*a + x^(2:ℕ)*y^(3:ℕ)*b + (2:ℂ)*x^(2:ℕ)*y^(2:ℕ) + (-2:ℂ)*x^(2:ℕ)*y*a^(2:ℕ)*b + x^(2:ℕ)*y*b + (-1:ℂ)*x^(2:ℕ)*z + (-1:ℂ)*x^(2:ℕ) + (-2:ℂ)*x*y*a*b + (-1:ℂ)*y^(2:ℕ) + (-3:ℂ))) = (x^(4:ℕ)*a)*0 + ((-1:ℂ))*((x*a)*((-1:ℂ)*x^(10:ℕ)*a + (-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ)*a + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(4:ℕ)*a^(3:ℕ) + x^(4:ℕ)*a + x^(3:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*a^(2:ℕ) + x^(2:ℕ)*y*a^(3:ℕ)*b + (-1:ℂ)*x^(2:ℕ)*y*a*b + x*y^(2:ℕ) + x*y*a^(2:ℕ)*b + x + a)) + ((-1:ℂ))*((x*a)*((-1:ℂ)*x^(10:ℕ)*a + x^(9:ℕ)*y*b + (-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + x^(9:ℕ) + x^(8:ℕ)*y*a*b + x^(7:ℕ)*y*b + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (3:ℂ)*x^(7:ℕ) + x^(6:ℕ)*y*a*b + (-1:ℂ)*x^(6:ℕ)*a^(3:ℕ) + x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y^(2:ℕ) + x^(5:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*y*b + (-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + x^(5:ℕ) + (2:ℂ)*x^(4:ℕ)*y*a*b + x^(4:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(3:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y^(2:ℕ) + x^(3:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(3:ℕ)*y*b + x^(3:ℕ)*z + x^(3:ℕ)*a^(2:ℕ) + x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*a^(3:ℕ)*b + (3:ℂ)*x^(2:ℕ)*y*a*b + (-1:ℂ)*x*y*a^(2:ℕ)*b + x*y*b + (2:ℂ)*x + (-1:ℂ)*a)) + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(2:ℕ)*y*a*b)*(((1:ℂ))*((1:ℂ))) + (x^(2:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3912_27 (x y z a b : ℂ) :
    (x)*0 = (x^(4:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ))*0 + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + (x^(2:ℕ)*y*a*b)*0 + (x^(2:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3912_3 (x y z a b : ℂ) :
    (x)*0 = (x^(4:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ))*0 + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(2:ℕ)*y*a*b)*0 + (x^(2:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*(((1:ℂ))*((1:ℂ))) := by ring1

compact_certificate theorem combination0_3912_41 (x y z a b : ℂ) :
    (x)*0 = (x^(4:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*((x^(4:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + ((-1:ℂ))*0 + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(2:ℕ)*y*a*b)*0 + (x^(2:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3912_42 (x y z a b : ℂ) :
    (x)*(((1:ℂ))*((2:ℂ)*x^(8:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(7:ℕ)*y*a*b + (2:ℂ)*x^(7:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a*b + (2:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(4:ℕ)*y*b + x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y*a*b + (2:ℂ)*x^(3:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ)*b^(2:ℕ) + x^(2:ℕ)*y^(2:ℕ) + (-2:ℂ)*x^(2:ℕ)*y*b + (2:ℂ)*x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ) + x*a + (-3:ℂ))) = (x^(4:ℕ)*a)*0 + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(8:ℕ)*a^(3:ℕ) + (-1:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + (-1:ℂ)*x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*a^(4:ℕ) + x^(3:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*a^(3:ℕ) + x^(2:ℕ)*a + (2:ℂ)*x + a)) + ((-1:ℂ))*(((1:ℂ))*((-1:ℂ)*x^(9:ℕ)*a^(2:ℕ) + x^(8:ℕ)*y*a*b + (-1:ℂ)*x^(8:ℕ)*a^(3:ℕ) + x^(8:ℕ)*a + x^(7:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y*a*b + x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*a^(2:ℕ)*b + x^(5:ℕ)*y*b + x^(5:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a + (2:ℂ)*x^(4:ℕ)*y*a*b + (-2:ℂ)*x^(4:ℕ)*a^(3:ℕ) + (4:ℂ)*x^(4:ℕ)*a + x^(3:ℕ)*y^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ) + (2:ℂ)*x^(3:ℕ)*y*b + x^(3:ℕ)*a^(4:ℕ) + (-3:ℂ)*x^(3:ℕ)*a^(2:ℕ) + x^(3:ℕ) + x^(2:ℕ)*a^(3:ℕ) + (-2:ℂ)*x^(2:ℕ)*a + x + (-1:ℂ)*a)) + (x^(3:ℕ))*(((1:ℂ))*(x*a + (1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(2:ℕ)*y*a*b)*0 + (x^(2:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3912_66 (x y z a b : ℂ) :
    (x)*0 = (x^(4:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ))*0 + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(2:ℕ)*y*a*b)*(((1:ℂ))*((1:ℂ))) + (x^(2:ℕ)*y*a*b)*(((1:ℂ))*((-1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3912_72 (x y z a b : ℂ) :
    (x)*((x)*((2:ℂ)*x^(7:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(6:ℕ)*y*a*b + x^(6:ℕ)*a + (-1:ℂ)*x^(5:ℕ)*y*b + (2:ℂ)*x^(5:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ) + x^(4:ℕ)*y*a*b + (-2:ℂ)*x^(4:ℕ)*a + (-1:ℂ)*x^(3:ℕ)*y^(2:ℕ)*b^(2:ℕ) + x^(3:ℕ)*y^(2:ℕ) + (2:ℂ)*x^(3:ℕ)*y*a^(2:ℕ)*b + (-2:ℂ)*x^(3:ℕ)*y*b + (-1:ℂ)*x^(3:ℕ)*a^(2:ℕ) + x^(3:ℕ) + (-1:ℂ)*x^(2:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + (-1:ℂ)*x^(2:ℕ)*y*a*b + (3:ℂ)*x^(2:ℕ)*a + (3:ℂ)*x*a^(2:ℕ) + (-3:ℂ)*x + (-1:ℂ)*a)) = (x^(4:ℕ)*a)*0 + ((-1:ℂ))*((x)*((-1:ℂ)*x^(8:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(7:ℕ)*a + (-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(5:ℕ)*y*a*b + (-1:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*a^(2:ℕ) + (-1:ℂ)*x^(4:ℕ) + (-1:ℂ)*x^(3:ℕ)*a + (-2:ℂ)*x^(2:ℕ)*a^(2:ℕ) + (2:ℂ)*x^(2:ℕ) + (-1:ℂ)*x*a^(3:ℕ) + (2:ℂ)*x*a + a^(2:ℕ))) + ((-1:ℂ))*((x)*((-1:ℂ)*x^(8:ℕ)*a^(2:ℕ) + x^(7:ℕ)*y*a*b + x^(6:ℕ)*y*b + (-1:ℂ)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ) + (2:ℂ)*x^(5:ℕ)*a + x^(4:ℕ)*y^(2:ℕ)*b^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y^(2:ℕ) + (-1:ℂ)*x^(4:ℕ)*y*a^(2:ℕ)*b + (2:ℂ)*x^(4:ℕ)*y*b + x^(4:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a*b^(2:ℕ) + x^(3:ℕ)*y*a*b + (-1:ℂ)*x^(3:ℕ)*a + (-1:ℂ)*x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ) + x*a^(3:ℕ) + (-1:ℂ)*x*a + (-1:ℂ)*a^(2:ℕ))) + (x^(3:ℕ))*((x)*(x + a)) + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(2:ℕ)*y*a*b)*0 + (x^(2:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3912_79 (x y z a b : ℂ) :
    (x)*0 = (x^(4:ℕ)*a)*((y^(2:ℕ))*((1:ℂ))) + ((-1:ℂ))*0 + ((-1:ℂ))*((x^(4:ℕ)*y^(2:ℕ)*a)*((1:ℂ))) + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(2:ℕ)*y*a*b)*0 + (x^(2:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3912_84 (x y z a b : ℂ) :
    (x)*0 = (x^(4:ℕ)*a)*0 + ((-1:ℂ))*0 + ((-1:ℂ))*0 + (x^(3:ℕ))*((x*a)*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*a)*(((1:ℂ))*((1:ℂ))) + (x^(2:ℕ)*y*a*b)*0 + (x^(2:ℕ)*y*a*b)*0 + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

compact_certificate theorem combination0_3912_9 (x y z a b : ℂ) :
    (x)*0 = (x^(4:ℕ)*a)*((y)*((-1:ℂ)*b)) + ((-1:ℂ))*0 + ((-1:ℂ))*0 + (x^(3:ℕ))*0 + ((-1:ℂ)*x^(4:ℕ)*a)*0 + (x^(2:ℕ)*y*a*b)*0 + (x^(2:ℕ)*y*a*b)*((x^(2:ℕ))*((1:ℂ))) + ((-1:ℂ)*x^(4:ℕ)*y^(2:ℕ)*a)*0 := by ring1

end QuantitativeArithmeticSmallLevelNineteenPoleLeading
end
