module

public import QuantitativeSpectralObservabilityFundamentalTailV1
public import QuantitativeSpectralObservabilityFundamentalCoordinatesV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticRegularTrace AsymptoticOrbitDiagonal
open QuantitativeSpectralFiniteReduction AsymptoticCongruenceLabels
open scoped lp Modular Pointwise

attribute [local instance] Classical.propDecidable

theorem fundamentalSet_subset_openCover (N : ℕ) : fundamentalSet N⊆openCover N := by
  intro z hz
  obtain ⟨q,w,hw,rfl⟩ := mem_iUnion.mp hz
  apply mem_iUnion.mpr
  refine ⟨q,w,?_,rfl⟩
  have hr : |w.re|≤(1:ℝ)/2 := hw.2
  have hi := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hw
  have hy : (1:ℝ)/4<w.im := by nlinarith [w.im_pos]
  exact ⟨by linarith [(abs_le.mp hr).1],by linarith [(abs_le.mp hr).2],hy⟩

theorem fundamentalSubsetProjection_formula (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (s : Set ℍ) (x : ℍ) :
    fundamentalSubsetProjection N hε ht s x=
      ((fundamentalTransfer N hε ht x).comp (corner s x)).comp
        (fundamentalTransfer N hε ht x).adjoint := by
  simp only [fundamentalSubsetProjection,fundamentalTransport,adjoint_comp,corner_adjoint]
  calc
    _ = ((fundamentalTransfer N hε ht x).comp ((corner s x).comp (corner s x))).comp
      (fundamentalTransfer N hε ht x).adjoint := by simp only [comp_assoc]
    _ = _ := by simp only [corner_idempotent]

theorem fundamentalTransfer_adjoint_coordinate (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (hx : fundamentalGood N x)
    (u : ℓ²(OrbitGroup,ℂ)) (hu : u∈quotientSpace N hε ht x) (g : OrbitGroup) :
    (fundamentalTransfer N hε ht x).adjoint u g=
      if g • x∈fundamentalSet N then coordinate N ε t x g u else 0 := by
  simp only [fundamentalTransfer,dite_eq_left hx,adjoint_comp,adjoint_adjoint,comp_apply]
  change fundamentalInduction N x hx ((induction N hε ht x).toContinuousLinearMap.adjoint u) g=_
  rw [fundamentalInduction_apply,← coordinate_eq_adjoint_of_quotient N hε ht x u hu g]
  by_cases hg : g • x∈fundamentalSet N
  · simp only [fundamentalAmplitude,Set.indicator_of_mem hg,one_mul,ite_eq_left hg]
  · simp only [fundamentalAmplitude,Set.indicator_of_notMem hg,zero_mul,ite_eq_right hg]

/-- An actual quotient vector is reconstructed on a retained quotient
corner from any bounded row giving its literal coordinates there. -/
theorem fundamentalSubsetProjection_of_coordinates (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) {s : Set ℍ} (hs : s⊆fundamentalSet N)
    (x : ℍ) (hx : fundamentalGood N x) (u r : ℓ²(OrbitGroup,ℂ))
    (hu : u∈quotientSpace N hε ht x)
    (hr : ∀ g, g • x∈s → coordinate N ε t x g u=r g) :
    fundamentalSubsetProjection N hε ht s x u=
      fundamentalTransfer N hε ht x (corner s x r) := by
  have he : corner s x ((fundamentalTransfer N hε ht x).adjoint u)=corner s x r := by
    apply lp.ext
    funext g
    simp only [corner_apply]
    by_cases hg : g • x∈s
    · simp only [ite_eq_left hg]
      exact (fundamentalTransfer_adjoint_coordinate N hε ht x hx u hu g).trans
        ((ite_eq_left (hs hg)).trans (hr g hg))
    · simp only [ite_eq_right hg]
  simp only [fundamentalSubsetProjection_formula,comp_apply]
  exact congrArg (fundamentalTransfer N hε ht x) he

def fundamentalRetained (N : ℕ) (H : ℝ) : Set ℍ :=
  fundamentalSet N \ wideTailCover N H

theorem fundamentalRetained_measurable (N : ℕ) (hN : 0<N) (H : ℝ) :
    MeasurableSet (fundamentalRetained N H) :=
  (fundamentalSet_measurable N hN).diff (wideTailCover_measurable N hN H)

theorem fundamentalRetained_subset_cover (N : ℕ) (H : ℝ) :
    fundamentalRetained N H⊆openCover N \ wideTailCover N H :=
  fun _ hz => ⟨fundamentalSet_subset_openCover N hz.1,hz.2⟩

#print axioms fundamentalSet_subset_openCover
#print axioms fundamentalTransfer_adjoint_coordinate
#print axioms fundamentalSubsetProjection_of_coordinates

end QuantitativeSpectralObservability
