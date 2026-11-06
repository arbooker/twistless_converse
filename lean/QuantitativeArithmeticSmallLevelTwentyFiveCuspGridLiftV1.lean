module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxSymbolicRowsV1
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveCuspLift
open QuantitativeArithmeticSevenLaurentRows

def liftPoly (p : Poly) : Poly := p.map (fun t => (t.1,7*t.2.1,t.2.2))

theorem eval_liftPoly (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c v (liftPoly p)=eval x y z w a b c (fun j => v (7*j)) p := by
  simp only [liftPoly,eval,List.map_map,Function.comp_def]

#print axioms eval_liftPoly
end QuantitativeArithmeticSmallLevelTwentyFiveCuspLift
