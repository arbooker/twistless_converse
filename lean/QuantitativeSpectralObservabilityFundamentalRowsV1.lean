module

public import QuantitativeSpectralObservabilityFundamentalCoordinatesV1
public import QuantitativeSpectralExceptionalFundamentalAssemblyV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set ContinuousLinearMap
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open AsymptoticRegularBranchFamily AsymptoticOrbitDiagonal
open QuantitativeSpectralExceptionalReducedRows
open scoped MatrixGroups BigOperators lp

attribute [local instance] Classical.propDecidable

theorem fundamentalReducedFamily_coordinate_row {I : Type*} [Fintype I]
    (N : ℕ) (hN : 0<N) (H : ℝ) (b : I → Branch) (γ : I → SL(2,ℤ))
    (hγ : ∀ i, γ i∈CongruenceSubgroup.Gamma0 N) (c : I → ℂ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (x : ℍ) (hx : fundamentalGood N x) (v : ℓ²(OrbitGroup,ℂ)) (g : OrbitGroup)
    (hred : ∀ i, ((integralLabel (γ i)*label (b i))*g) • x∈fundamentalCompact N H) :
    fundamentalReducedFamily N hN H b γ c hε t x v g=
      ∑ i, c i*coordinate N ε t x (label (b i)*g) (fundamentalSampling N hN H hε ht x v) := by
  simp only [fundamentalReducedFamily,_root_.sum_apply,smul_apply,lp.coeFn_sum,
    Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,comp_apply,pull_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hm : integralLabel (γ i)∈gamma N :=
    (integralLabel_mem_gamma_iff N (γ i)).mpr (hγ i)
  have he := fundamentalSampling_reduced_coordinate N hN H hε ht x hx v
    ⟨integralLabel (γ i),hm⟩ (label (b i)*g) (by simpa only [mul_assoc] using hred i)
  simpa only [mul_assoc] using congrArg (fun z : ℂ => c i*z) he.symm

private theorem sum_piecewise_disjoint {K X : Type*} [Fintype K]
    (E : K → Set X) (hd : Pairwise (fun i j => Disjoint (E i) (E j)))
    (x : X) (a : ℂ) :
    (∑ j, if x∈E j then a else 0)=if x∈⋃ j,E j then a else 0 := by
  classical
  by_cases hx : x∈⋃ j,E j
  · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    rw [ite_eq_left hx,Finset.sum_eq_single j]
    · exact ite_eq_left hj
    · intro i _ hij
      exact ite_eq_right (fun hi => Set.disjoint_left.mp (hd hij) hi hj)
    · simp
  · have hn (j : K) : x∉E j := fun hj => hx (mem_iUnion.mpr ⟨j,hj⟩)
    simp only [ite_eq_right hx,ite_eq_right (hn _),Finset.sum_const_zero]

/-- The selected bounded operator is precisely the retained literal
quotient residual of the normalized sampler, independently of the selected
congruence representatives. -/
theorem selectedFundamentalFamily_coordinate_row {I K : Type*} [Fintype I] [Fintype K]
    (N : ℕ) (hN : 0<N) (H : ℝ) (b : I → Branch) (w : K → I → List SL(2,ℤ))
    (hw : ∀ j i, (w j i).prod∈CongruenceSubgroup.Gamma0 N) (c : I → ℂ)
    (E : K → Set ℍ) (hd : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hred : ∀ j i z, z∈E j →
      (integralLabel (w j i).prod*label (b i)) • z∈fundamentalCompact N H)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (x : ℍ) (hx : fundamentalGood N x) (v : ℓ²(OrbitGroup,ℂ)) (g : OrbitGroup) :
    selectedFundamentalFamily N hN H b w c E hε t x v g=
      if g • x∈⋃ j,E j then
        ∑ i, c i*coordinate N ε t x (label (b i)*g)
          (fundamentalSampling N hN H hε ht x v) else 0 := by
  simp only [selectedFundamentalFamily,_root_.sum_apply,lp.coeFn_sum,
    Finset.sum_apply,comp_apply,corner_apply]
  calc
    _ = ∑ j, if g • x∈E j then
        ∑ i, c i*coordinate N ε t x (label (b i)*g)
          (fundamentalSampling N hN H hε ht x v) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hg : g • x∈E j
      · rw [ite_eq_left hg,ite_eq_left hg]
        exact fundamentalReducedFamily_coordinate_row N hN H b (fun i => (w j i).prod)
          (hw j) c hε ht x hx v g (fun i => by
            simpa only [mul_smul] using hred j i (g • x) hg)
      · simp only [ite_eq_right hg]
    _ = _ := sum_piecewise_disjoint E hd (g • x) _

#print axioms fundamentalReducedFamily_coordinate_row
#print axioms selectedFundamentalFamily_coordinate_row

end QuantitativeSpectralObservability
