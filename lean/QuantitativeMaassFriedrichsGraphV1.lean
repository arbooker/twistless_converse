module

public import QuantitativeMaassFriedrichsResolventV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

/-- The unshifted quotient realization defined by the actual energy
resolvent. Thus `y=Δ_F x` precisely when `(1+Δ_F)⁻¹(x+y)=x`. -/
def FriedrichsGraph (N : ℕ) (x y : AutomorphicSpace N) : Prop :=
  friedrichsResolvent N (x+y)=x

def FriedrichsAdjointGraph (N : ℕ) (x y : AutomorphicSpace N) : Prop :=
  ∀ f g : AutomorphicSpace N, FriedrichsGraph N f g → inner ℂ g x=inner ℂ f y

theorem friedrichsGraph_resolvent (N : ℕ) (z : AutomorphicSpace N) :
    FriedrichsGraph N (friedrichsResolvent N z) (z-friedrichsResolvent N z) := by
  simp [FriedrichsGraph]

theorem friedrichsGraph_singleValued (N : ℕ) {x y z : AutomorphicSpace N}
    (hy : FriedrichsGraph N x y) (hz : FriedrichsGraph N x z) : y=z :=
  add_left_cancel (friedrichsResolvent_injective N (hy.trans hz.symm))

theorem friedrichsGraph_symmetric (N : ℕ) {x y f g : AutomorphicSpace N}
    (hxy : FriedrichsGraph N x y) (hfg : FriedrichsGraph N f g) :
    inner ℂ y f=inner ℂ x g := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (friedrichsResolvent_isSelfAdjoint N) (x+y) (f+g)
  change inner ℂ (friedrichsResolvent N (x+y)) (f+g)=
    inner ℂ (x+y) (friedrichsResolvent N (f+g)) at hs
  rw [hxy,hfg,inner_add_right,inner_add_left] at hs
  exact (add_left_cancel hs).symm

/-- Equality with the full adjoint pairing graph, not merely formal
symmetry. The converse tests against every vector in the actual resolvent
range and uses the proved self-adjoint bounded resolvent. -/
theorem friedrichsGraph_iff_adjoint (N : ℕ) (x y : AutomorphicSpace N) :
    FriedrichsGraph N x y ↔ FriedrichsAdjointGraph N x y := by
  constructor
  · intro h f g hfg
    exact friedrichsGraph_symmetric N hfg h
  · intro h
    apply ext_inner_left ℂ
    intro z
    have ht := h (friedrichsResolvent N z) (z-friedrichsResolvent N z)
      (friedrichsGraph_resolvent N z)
    rw [inner_sub_left] at ht
    have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (friedrichsResolvent_isSelfAdjoint N) z (x+y)
    change inner ℂ (friedrichsResolvent N z) (x+y)=
      inner ℂ z (friedrichsResolvent N (x+y)) at hs
    rw [← hs,inner_add_right,← ht]
    ring

theorem friedrichsGraph_denseDomain (N : ℕ) :
    Dense {x : AutomorphicSpace N | ∃ y, FriedrichsGraph N x y} := by
  apply (friedrichsResolvent_denseRange N).mono
  rintro x ⟨z,rfl⟩
  exact ⟨_,friedrichsGraph_resolvent N z⟩

theorem friedrichsGraph_closed (N : ℕ) :
    IsClosed {p : AutomorphicSpace N × AutomorphicSpace N | FriedrichsGraph N p.1 p.2} :=
  isClosed_eq ((friedrichsResolvent N).continuous.comp (continuous_fst.add continuous_snd))
    continuous_fst

theorem friedrichsGraph_nonnegative (N : ℕ) {x y : AutomorphicSpace N}
    (h : FriedrichsGraph N x y) : 0≤(inner ℂ x y).re := by
  have hl := friedrichsResolvent_lower N (x+y)
  rw [h,inner_add_right,Complex.add_re] at hl
  have hself : (inner ℂ x x).re=‖x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [hself] at hl
  linarith

theorem friedrichsGraph_extends_quotientLaplacian (N : ℕ) (x : quotientLaplacianDomain N) :
    FriedrichsGraph N x.val (quotientLaplacian N x) := friedrichsResolvent_shifted N x

/-- The constructed self-adjoint realization agrees with the actual
differential Laplacian on every smooth compact Poincaré vector. -/
theorem friedrichsGraph_poincareSeed (N : ℕ) (u : SmoothUpperSeed) :
    FriedrichsGraph N (poincareSeedVector N u) (poincareSeedVector N u.laplacian) := by
  have h := friedrichsGraph_extends_quotientLaplacian N
    ⟨poincareSeedVector N u,poincareSeedVector_mem_quotientLaplacianDomain N u⟩
  rw [quotientLaplacian_poincareSeed] at h
  exact h

#print axioms friedrichsGraph_iff_adjoint
#print axioms friedrichsGraph_nonnegative
#print axioms friedrichsGraph_poincareSeed

end QuantitativeMaass
