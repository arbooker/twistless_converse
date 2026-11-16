module

public import QuantitativeMaassLVDeficitOperatorV1
public import QuantitativeMaassLVGeometricLowerV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass

local instance (N : ℕ) : Ring (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.ring
local instance (N : ℕ) : Algebra ℝ (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.algebra

/-- The actual multiplier of the complementary LV operator on a principal
joint Laplacian/Hecke eigenvector. -/
def lvDeficitMultiplier (p d : ℕ) (r τ : ℝ) : ℝ :=
  (1-(τ-2*Real.cos (Real.log p*r))^2/(lvBound p)^2)^d

theorem lvDeficitMultiplier_square (p d : ℕ) (r τ : ℝ) :
    (lvDeficitMultiplier p d r τ)^2=1-lvScalarSymbol p (2*d) (τ,r) := by
  simp only [lvDeficitMultiplier,lvScalarSymbol,sub_sub_cancel,←pow_mul]
  rw [Nat.mul_comm d 2]

theorem actualLVDeficit_eigen (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (v : AutomorphicSpace N) (r τ : ℝ)
    (hgraph : FriedrichsGraph N v (((1/4+r^2:ℝ):ℂ) • v))
    (hHecke : HeckeL2.operator N p hN hpN a b hab v=(τ:ℂ) • v) (d : ℕ) :
    actualLVDeficit N p hN hpN a b hab d v=(lvDeficitMultiplier p d r τ:ℂ) • v := by
  let z : ℂ := ((τ-2*Real.cos (Real.log p*r):ℝ):ℂ)
  let c : ℝ := ((lvBound p)^2)⁻¹
  have hD : lvDifference N p hN hpN a b hab v=z • v := by
    simp only [lvDifference,sub_apply,smul_apply,hHecke,
      Wave.shiftedQuotientWave_principal N r hgraph (Real.log p),smul_smul]
    dsimp only [z]
    simp only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat]
    exact (sub_smul (τ:ℂ) (2*(Real.cos (Real.log p*r):ℂ)) v).symm
  have hf := lvFilter_eigenvector (lvDifference N p hN hpN a b hab) v z hD c d
  have hcoef : (1-(1-(1-(c:ℂ)*z^2)^d))=(lvDeficitMultiplier p d r τ:ℂ) := by
    rw [sub_sub_cancel]
    dsimp only [lvDeficitMultiplier,z,c]
    push_cast
    congr 1
    ring
  change v-lvFilter (lvDifference N p hN hpN a b hab) c d v=_
  rw [hf]
  calc
    _ = (1-(1-(1-(c:ℂ)*z^2)^d)) • v := by
      simpa only [one_smul] using (sub_smul (1:ℂ) (1-(1-(c:ℂ)*z^2)^d) v).symm
    _ = _ := by rw [hcoef]

#print axioms lvDeficitMultiplier_square
#print axioms actualLVDeficit_eigen
end QuantitativeMaass
