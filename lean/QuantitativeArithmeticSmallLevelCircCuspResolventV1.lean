module

public import QuantitativeArithmeticSmallLevelCircCuspBoundaryV1
public import QuantitativeArithmeticSmallLevelCircModularHeckeTheoryV4

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc.CuspSpectral

open UpperHalfPlane AsymptoticClassicalCusp

/-- Boundary spectral exclusion for every positive even weight. -/
theorem boundary_eigen_zero (N p m : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) (hm : 0 < m)
    (f : CuspForm (level N) ((2 * m : ℕ) : ℤ))
    (hf : dilationTrace N p hp.pos ((2 * m : ℕ) : ℤ) f =
      (1 + (p : ℂ)^(2 * m - 1)) • f) : f = 0 := by
  by_cases hm1 : m = 1
  · subst m
    change dilationTrace N p hp.pos 2 f = (1 + (p : ℂ)^1) • f at hf
    have hh : dilationTrace N p hp.pos 2 f = (p + 1 : ℂ) • f := by
      simpa only [pow_one, add_comm] using hf
    exact weight_two_boundary_eigen_zero N p hN hp hpN f hh
  · exact higher_boundary_eigen_zero N p m hN hp hpN (by omega) f hf

def boundaryDifference (N p m : ℕ) [NeZero N] (hp : 0 < p) :
    CuspForm (level N) ((2 * m : ℕ) : ℤ) →ₗ[ℂ]
      CuspForm (level N) ((2 * m : ℕ) : ℤ) :=
  (1 + (p : ℂ)^(2 * m - 1)) • LinearMap.id -
    dilationTrace N p hp ((2 * m : ℕ) : ℤ)

theorem boundaryDifference_injective (N p m : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) (hm : 0 < m) :
    Function.Injective (boundaryDifference N p m hp.pos) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  apply boundary_eigen_zero N p m hN hp hpN hm f
  exact (sub_eq_zero.mp hf).symm

/-- The actual cusp resolvent at the Eisenstein boundary eigenvalue. -/
def boundaryResolvent (N p m : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) (hm : 0 < m) :
    CuspForm (level N) ((2 * m : ℕ) : ℤ) ≃ₗ[ℂ]
      CuspForm (level N) ((2 * m : ℕ) : ℤ) :=
  (LinearEquiv.ofInjectiveEndo (boundaryDifference N p m hp.pos)
    (boundaryDifference_injective N p m hN hp hpN hm)).symm

theorem boundaryDifference_resolvent (N p m : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) (hm : 0 < m)
    (f : CuspForm (level N) ((2 * m : ℕ) : ℤ)) :
    boundaryDifference N p m hp.pos (boundaryResolvent N p m hN hp hpN hm f) = f :=
  (LinearEquiv.ofInjectiveEndo (boundaryDifference N p m hp.pos)
    (boundaryDifference_injective N p m hN hp hpN hm)).apply_symm_apply f

/-- The full modular Hecke operator restricts to the previously constructed
classical cusp operator. No eigenbasis identification is used. -/
theorem dilationTrace_toModular (N p : ℕ) [NeZero N] (hp : 0 < p)
    (k : ℤ) (f : CuspForm (level N) k) :
    ModularHecke.dilationTrace N p hp k (CuspForm.toModularFormₗ f) =
      CuspForm.toModularFormₗ (dilationTrace N p hp k f) := by
  apply ModularForm.ext
  intro z
  rfl

#print axioms boundary_eigen_zero
#print axioms boundaryDifference_injective
#print axioms boundaryResolvent
#print axioms boundaryDifference_resolvent
#print axioms dilationTrace_toModular

end QuantitativeArithmeticSmallLevelCirc.CuspSpectral
