module

public import QuantitativeMaassEigenfamilyFiniteV1
public import QuantitativeMaassHilbertSchmidtIdealV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Change of Hilbert metric represented on the original space. -/
def similarityOperator (L : H ≃L[ℂ] H) (B : H →L[ℂ] H) : H →L[ℂ] H :=
  L.toContinuousLinearMap.comp (B.comp L.symm.toContinuousLinearMap)

omit [CompleteSpace H] in
theorem similarityOperator_eigen (L : H ≃L[ℂ] H) (B : H →L[ℂ] H)
    (x : H) (c : ℂ) (hx : B x=c • x) :
    similarityOperator L B (L x)=c • L x := by
  simp only [similarityOperator,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply,hx,map_smul]

theorem similarityOperator_summable (basis : HilbertBasis ι ℂ H)
    (L : H ≃L[ℂ] H) (B : H →L[ℂ] H)
    (hB : Summable (fun i => ‖B (basis i)‖^2)) :
    Summable (fun i => ‖similarityOperator L B (basis i)‖^2) :=
  (left_comp_energy_bound basis L.toContinuousLinearMap
    (B.comp L.symm.toContinuousLinearMap)
    (right_comp_energy_bound basis B L.symm.toContinuousLinearMap hB).1).1

/-- Exact counting after a metric change. The target contribution is kept
as its own squared-column sum, without a metric-equivalence constant. -/
theorem similarity_count_source_split (basis : HilbertBasis ι ℂ H)
    (L : H ≃L[ℂ] H) (B : H →L[ℂ] H)
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (v : κ → H) (hv : LinearIndependent ℂ v) (h : κ → ℝ)
    (he : ∀ i,B (v i)=(h i:ℂ) • v i) (hl : ∀ i,1≤h i)
    (hB : Summable (fun i => ‖B (basis i)‖^2)) :
    Finite κ ∧ (Nat.card κ:ℝ)≤
      hilbertSchmidtEnergy basis ((similarityOperator L B).comp W.starProjection)+
      hilbertSchmidtEnergy basis ((similarityOperator L B).comp Wᗮ.starProjection) := by
  have hvL : LinearIndependent ℂ (fun i => L (v i)) :=
    (L.toLinearMap.linearIndependent_iff_of_injOn L.injective.injOn).mpr hv
  have hs := similarityOperator_summable basis L B hB
  obtain ⟨hf,hc⟩ := independent_eigenfamily_finite basis (similarityOperator L B)
    (fun i => L (v i)) hvL h (fun i => similarityOperator_eigen L B _ _ (he i)) hl hs
  rw [source_projection_energy_split basis W (similarityOperator L B) hs] at hc
  exact ⟨hf,hc⟩

/-- Only the excess receives the metric-equivalence constant, provided the
inverse metric change is the identity on the orthogonal complement. The
actual target metric and its canonical spectral trace remain to be supplied
by the geometric application. -/
theorem similarity_count_target_excess (basis : HilbertBasis ι ℂ H)
    (L : H ≃L[ℂ] H) (B : H →L[ℂ] H)
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (hL : ∀ x,L.symm (Wᗮ.starProjection x)=Wᗮ.starProjection x)
    (v : κ → H) (hv : LinearIndependent ℂ v) (h : κ → ℝ)
    (he : ∀ i,B (v i)=(h i:ℂ) • v i) (hl : ∀ i,1≤h i)
    (hB : Summable (fun i => ‖B (basis i)‖^2)) :
    Finite κ ∧ (Nat.card κ:ℝ)≤
      hilbertSchmidtEnergy basis ((similarityOperator L B).comp W.starProjection)+
      ‖L.toContinuousLinearMap‖^2 * hilbertSchmidtEnergy basis (B.comp Wᗮ.starProjection) := by
  obtain ⟨hf,hc⟩ := similarity_count_source_split basis L B W v hv h he hl hB
  have hcomp : (similarityOperator L B).comp Wᗮ.starProjection=
      L.toContinuousLinearMap.comp (B.comp Wᗮ.starProjection) := by
    ext x : 1
    simp only [similarityOperator,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,hL]
  rw [hcomp] at hc
  have hb := (left_comp_energy_bound basis L.toContinuousLinearMap
    (B.comp Wᗮ.starProjection) (projected_source_summable basis Wᗮ B hB)).2
  exact ⟨hf,hc.trans (add_le_add le_rfl hb)⟩

#print axioms similarityOperator_eigen
#print axioms similarityOperator_summable
#print axioms similarity_count_source_split
#print axioms similarity_count_target_excess

end QuantitativeMaass
