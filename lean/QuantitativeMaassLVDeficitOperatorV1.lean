module

public import QuantitativeMaassLVCuspidalProjectionV1
public import QuantitativeMaassShiftedWaveEigenV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open ContinuousLinearMap
namespace QuantitativeMaass

local instance (N : ℕ) : Ring (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.ring
local instance (N : ℕ) : Algebra ℝ (AutomorphicSpace N→L[ℂ]AutomorphicSpace N) := ContinuousLinearMap.algebra

variable (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)

/-- Complement of the literal LV filter. Its even powers measure the
finite-place deficit without subtracting two spectral counting estimates. -/
def actualLVDeficit (d : ℕ) : AutomorphicSpace N→L[ℂ]AutomorphicSpace N :=
  1-actualLVFilter N p hN hpN a b hab d

theorem actualLVDeficit_order (d : ℕ) :
    0≤actualLVDeficit N p hN hpN a b hab d ∧
      actualLVDeficit N p hN hpN a b hab d≤1 ∧
      ‖actualLVDeficit N p hN hpN a b hab d‖≤1 := by
  have h := actualLVFilter_order N p hN hpN a b hab d
  have h0 : 0≤actualLVDeficit N p hN hpN a b hab d := sub_nonneg.mpr h.2.1
  have h1 : actualLVDeficit N p hN hpN a b hab d≤1 := sub_le_self _ h.1
  exact ⟨h0,h1,(CStarAlgebra.norm_le_one_iff_of_nonneg (actualLVDeficit N p hN hpN a b hab d) h0).mpr h1⟩

theorem actualLVDeficit_selfAdjoint (d : ℕ) :
    IsSelfAdjoint (actualLVDeficit N p hN hpN a b hab d) :=
  (nonneg_iff_isPositive.mp (actualLVDeficit_order N p hN hpN a b hab d).1).isSelfAdjoint

theorem actualLVDeficit_square (d : ℕ) :
    (actualLVDeficit N p hN hpN a b hab d)^2=actualLVDeficit N p hN hpN a b hab (2*d) := by
  simp only [actualLVDeficit,actualLVFilter,lvFilter,sub_sub_cancel,←pow_mul]
  rw [Nat.mul_comm d 2]

/-- Squared deficit column energy is exactly the complementary LV trace
at twice the degree, a positive quantity on the whole quotient. -/
theorem actualLVDeficit_norm_square (d : ℕ) (v : AutomorphicSpace N) :
    ‖actualLVDeficit N p hN hpN a b hab d v‖^2=
      (inner ℂ (actualLVDeficit N p hN hpN a b hab (2*d) v) v).re := by
  let T := actualLVDeficit N p hN hpN a b hab d
  have hT := isSelfAdjoint_iff_isSymmetric.mp (actualLVDeficit_selfAdjoint N p hN hpN a b hab d)
  have hh := hT (T v) v
  change inner ℂ (T (T v)) v=inner ℂ (T v) (T v) at hh
  have he : T (T v)=actualLVDeficit N p hN hpN a b hab (2*d) v := by
    have hp := congrArg (fun U : AutomorphicSpace N→L[ℂ]AutomorphicSpace N => U v)
      (actualLVDeficit_square N p hN hpN a b hab d)
    simpa only [T,pow_two,ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_apply] using hp
  rw [he] at hh
  rw [←inner_self_eq_norm_sq (𝕜:=ℂ)]
  exact congrArg Complex.re hh.symm

theorem actualLVDeficit_cusp_projection_norm
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1) (d : ℕ) (v : AutomorphicSpace N) :
    ‖actualLVDeficit N p hN hpN a b hab d (localCuspidalProjection N hN v)‖≤
      ‖actualLVDeficit N p hN hpN a b hab d v‖ := by
  have hc : actualLVDeficit N p hN hpN a b hab d*localCuspidalProjection N hN=
      localCuspidalProjection N hN*actualLVDeficit N p hN hpN a b hab d := by
    simp only [actualLVDeficit,sub_mul,mul_sub,one_mul,mul_one,
      actualLVFilter_localCuspidalProjection N p hN hpN hNp hpres a b hab,
      localCuspidalProjection_actualLVFilter N p hN hpN hNp hpres a b hab]
  have he := congrArg (fun U : AutomorphicSpace N→L[ℂ]AutomorphicSpace N => U v) hc
  change actualLVDeficit N p hN hpN a b hab d (localCuspidalProjection N hN v)=
    localCuspidalProjection N hN (actualLVDeficit N p hN hpN a b hab d v) at he
  rw [he]
  exact (localCuspidalSpace N hN).norm_starProjection_apply_le _

#print axioms actualLVDeficit_order
#print axioms actualLVDeficit_selfAdjoint
#print axioms actualLVDeficit_square
#print axioms actualLVDeficit_norm_square
#print axioms actualLVDeficit_cusp_projection_norm
end QuantitativeMaass
