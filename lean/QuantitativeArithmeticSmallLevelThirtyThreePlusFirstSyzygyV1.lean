module
public import QuantitativeArithmeticSmallLevelThirtyThreeBaseRowsV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreePlusFirstSyzygy
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeLaurent
def block0 : Poly := [((1/1:ℚ),1,(-2,-1,-1,0,0,0,0)),((1/1:ℚ),1,(-1,-1,-1,0,1,0,0)),((-2/1:ℚ),2,(-2,-1,-1,0,0,0,0)),((-2/1:ℚ),2,(-1,-1,-1,0,1,0,0)),((1/1:ℚ),2,(-1,0,-1,0,1,0,0)),((-1/1:ℚ),2,(0,0,-1,0,0,0,0)),((1/1:ℚ),7,(-2,-1,0,0,0,0,0)),((1/1:ℚ),9,(-2,-1,0,0,0,0,0)),((-2/1:ℚ),10,(-2,0,-1,0,0,0,0)),((-1/1:ℚ),10,(-2,1,-1,0,0,0,0)),((1/1:ℚ),10,(0,0,-1,0,0,0,0)),((-1/1:ℚ),12,(-2,0,-1,0,0,0,0)),((-1/1:ℚ),12,(-2,1,-1,0,0,0,0)),((1/1:ℚ),43,(1,0,-1,0,1,0,0)),((1/1:ℚ),48,(-2,-1,0,0,0,0,0)),((1/1:ℚ),48,(-2,0,0,0,0,0,0)),((1/1:ℚ),53,(-2,-1,0,0,0,0,0)),((1/1:ℚ),53,(-2,0,0,0,0,0,0)),((-1/1:ℚ),57,(0,0,0,0,0,0,0)),((1/1:ℚ),65,(-2,-1,0,0,0,0,0)),((1/1:ℚ),65,(-1,-1,0,0,1,0,0)),((1/1:ℚ),66,(0,0,-1,0,0,0,0)),((1/1:ℚ),66,(1,0,-1,0,1,0,0)),((1/1:ℚ),69,(-2,-1,0,0,0,0,0))]
def block1 : Poly := [((1/1:ℚ),72,(-2,0,0,0,0,0,0)),((2/1:ℚ),668,(-2,0,-1,0,0,0,0)),((1/1:ℚ),668,(-2,1,-1,0,0,0,0)),((-1/1:ℚ),668,(0,0,-1,0,0,0,0)),((1/1:ℚ),672,(0,0,0,0,0,0,0)),((-1/1:ℚ),674,(-1,0,0,0,1,0,0)),((-1/1:ℚ),686,(-2,-1,0,0,0,0,0)),((-1/1:ℚ),723,(0,0,0,0,0,0,0)),((-1/1:ℚ),734,(0,0,0,0,0,0,0)),((1/1:ℚ),741,(0,-1,0,0,0,0,0)),((-1/1:ℚ),755,(-2,0,0,0,0,0,0)),((1/1:ℚ),756,(0,0,0,0,0,0,0))]
def operations : Poly := block0 ++ block1

theorem certificate : substituteCompute (baseRows 1) operations=[] := by decide +kernel

theorem annihilates (x y z a : ℂ) (w : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) :
    eval x y z 1 a 1 1 (fun j => eval x y z 1 a 1 1 w (baseRows 1 j)) operations=0 := by
  apply substitution_zero x y z 1 a 1 1 w hx hy hz (by norm_num)
  rw [← substituteCompute_eq]
  exact certificate

#print axioms certificate
#print axioms annihilates
end QuantitativeArithmeticSmallLevelThirtyThreePlusFirstSyzygy
