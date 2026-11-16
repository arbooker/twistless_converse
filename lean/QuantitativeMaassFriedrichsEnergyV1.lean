module

public import QuantitativeMaassQuotientNonnegativeV1
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
@[expose] public noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- A distinct type for the energy norm on the actual operator domain.
The existing quotient-domain norm is not altered. -/
def QuotientEnergyDomain (N : ℕ) : Type := quotientLaplacianDomain N

instance (N : ℕ) : AddCommGroup (QuotientEnergyDomain N) :=
  inferInstanceAs (AddCommGroup (quotientLaplacianDomain N))

instance (N : ℕ) : Module ℂ (QuotientEnergyDomain N) :=
  inferInstanceAs (Module ℂ (quotientLaplacianDomain N))

def energyDomainValue (N : ℕ) (x : QuotientEnergyDomain N) : AutomorphicSpace N :=
  (x : quotientLaplacianDomain N).val

def energyDomainLaplacian (N : ℕ) (x : QuotientEnergyDomain N) : AutomorphicSpace N :=
  quotientLaplacian N x

/-- The actual positive energy scalar product, not a supplied Hilbert
structure or an assumed closed form. -/
instance quotientEnergyCore (N : ℕ) : InnerProductSpace.Core ℂ (QuotientEnergyDomain N) where
  inner x y := inner ℂ (energyDomainValue N x) (energyDomainValue N y)+
    inner ℂ (energyDomainValue N x) (energyDomainLaplacian N y)
  conj_inner_symm x y := by
    simp only [map_add,inner_conj_symm]
    exact congrArg (inner ℂ (energyDomainValue N x) (energyDomainValue N y)+·)
      (quotientLaplacian_symmetric N x y)
  re_inner_nonneg x := by
    rw [map_add]
    exact add_nonneg (inner_self_nonneg (𝕜 := ℂ)) (quotientLaplacian_nonnegative N x)
  add_left x y z := by
    change inner ℂ (energyDomainValue N x+energyDomainValue N y) (energyDomainValue N z)+
      inner ℂ (energyDomainValue N x+energyDomainValue N y) (energyDomainLaplacian N z)=_
    simp only [inner_add_left]
    ring
  smul_left x y c := by
    change inner ℂ (c•energyDomainValue N x) (energyDomainValue N y)+
      inner ℂ (c•energyDomainValue N x) (energyDomainLaplacian N y)=_
    rw [inner_smul_left (energyDomainValue N x) (energyDomainValue N y) c,
      inner_smul_left (energyDomainValue N x) (energyDomainLaplacian N y) c]
    ring
  definite x hx := by
    have hr := congrArg Complex.re hx
    change (inner ℂ (energyDomainValue N x) (energyDomainValue N x)+
      inner ℂ (energyDomainValue N x) (energyDomainLaplacian N x)).re=0 at hr
    rw [Complex.add_re] at hr
    have hself : (inner ℂ (energyDomainValue N x) (energyDomainValue N x)).re=
        ‖energyDomainValue N x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
    rw [hself] at hr
    have hn := quotientLaplacian_nonnegative N x
    change 0≤(inner ℂ (energyDomainValue N x) (energyDomainLaplacian N x)).re at hn
    have hzero : ‖energyDomainValue N x‖=0 := by
      nlinarith [sq_nonneg ‖energyDomainValue N x‖,norm_nonneg (energyDomainValue N x)]
    exact Subtype.ext (norm_eq_zero.mp hzero)

instance quotientEnergyNormedAddCommGroup (N : ℕ) : NormedAddCommGroup (QuotientEnergyDomain N) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance quotientEnergyInnerProductSpace (N : ℕ) : InnerProductSpace ℂ (QuotientEnergyDomain N) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (QuotientEnergyDomain N))

theorem quotientEnergy_inner (N : ℕ) (x y : QuotientEnergyDomain N) :
    inner ℂ x y=inner ℂ (energyDomainValue N x) (energyDomainValue N y)+
      inner ℂ (energyDomainValue N x) (energyDomainLaplacian N y) := rfl

theorem quotientEnergy_norm_sq (N : ℕ) (x : QuotientEnergyDomain N) :
    ‖x‖^2=‖energyDomainValue N x‖^2+
      (inner ℂ (energyDomainValue N x) (energyDomainLaplacian N x)).re := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [quotientEnergy_inner] at h
  change (inner ℂ (energyDomainValue N x) (energyDomainValue N x)+
    inner ℂ (energyDomainValue N x) (energyDomainLaplacian N x)).re=‖x‖^2 at h
  rw [Complex.add_re] at h
  have hself : (inner ℂ (energyDomainValue N x) (energyDomainValue N x)).re=
      ‖energyDomainValue N x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hself] at h
  exact h.symm

theorem energyDomainValue_norm_le (N : ℕ) (x : QuotientEnergyDomain N) :
    ‖energyDomainValue N x‖≤‖x‖ := by
  have h := quotientEnergy_norm_sq N x
  have hn := quotientLaplacian_nonnegative N x
  change 0≤(inner ℂ (energyDomainValue N x) (energyDomainLaplacian N x)).re at hn
  nlinarith [norm_nonneg x,norm_nonneg (energyDomainValue N x)]

/-- Completion in the energy norm, built from the established quotient
operator and its nonnegative Green form. -/
abbrev QuotientEnergySpace (N : ℕ) := UniformSpace.Completion (QuotientEnergyDomain N)

#print axioms quotientEnergyCore
#print axioms energyDomainValue_norm_le

end QuantitativeMaass
