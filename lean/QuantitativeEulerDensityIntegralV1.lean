module

public import QuantitativeEulerDensityCompactV1
public import QuantitativeEulerDensityIntegerNormV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open AsymptoticCongruenceLabels QuantitativeEulerDiamondDecode
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups Classical

/-- Multiplied unimodular matrix defects agree exactly with their group
algebra realizations. This uses multiplicativity only on SL2(Z). -/
theorem matrixCompactAction_integral_defect {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (γ β : SL(2,ℤ)) :
    matrixCompactAction hs hε t x ((matrixSymbol γ.val-1)*matrixSymbol β.val)=
      compactAction hs hε t x ((symbol (integralLabel γ)-1)*symbol (integralLabel β)) := by
  rw [sub_mul,one_mul,map_sub,←matrixSymbol_mul]
  change matrixCompactAction hs hε t x (matrixSymbol (γ*β).val)-
    matrixCompactAction hs hε t x (matrixSymbol β.val)=_
  rw [matrixCompactAction_integral,matrixCompactAction_integral]
  have hm : symbol (integralLabel (γ*β))=
      symbol (integralLabel γ)*symbol (integralLabel β) :=
    (congrArg symbol (integralLabel.map_mul γ β)).trans
      (symbol.map_mul (integralLabel γ) (integralLabel β))
  have he : (symbol (integralLabel γ)-1)*symbol (integralLabel β)=
      symbol (integralLabel (γ*β))-symbol (integralLabel β) := by
    calc
      _ = symbol (integralLabel γ)*symbol (integralLabel β)-1*symbol (integralLabel β) := sub_mul _ _ _
      _ = symbol (integralLabel γ)*symbol (integralLabel β)-symbol (integralLabel β) :=
        congrArg (fun z : Ring => symbol (integralLabel γ)*symbol (integralLabel β)-z) (one_mul _)
      _ = _ := congrArg (fun z : Ring => z-symbol (integralLabel β)) hm.symm
  rw [he]
  exact (map_sub (compactAction hs hε t x) _ _).symm

theorem matrixCompactAction_integral_defect_norm (γ β : SL(2,ℤ))
    {s : Set ℍ} (hs : IsCompact s) {B H ε : ℝ}
    (hB : 0≤B) (hb : MatrixEntryBound β.val B) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖matrixCompactAction hs hε t x ((matrixSymbol γ.val-1)*matrixSymbol β.val) v‖≤
      (integerCompactDistortion B H)^t*
        ‖AsymptoticCongruenceDefect.operator γ
          (branchImage_compact (symbolBranch (integralLabel β)) hs) hε t x v‖ := by
  rw [matrixCompactAction_integral_defect]
  have h := compactAction_mul_integral_norm β (symbol (integralLabel γ)-1)
    hs hB hb hε hre him t x v
  rw [compactAction_congruence] at h
  exact h

#print axioms matrixCompactAction_integral_defect
#print axioms matrixCompactAction_integral_defect_norm
end QuantitativeEulerDensityGenerators
