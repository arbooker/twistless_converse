module

public import QuantitativeMaassMetricColumnExcessV1
public import QuantitativeMaassScalarMetricProjectionV1
public import QuantitativeMaassIsometricExcessTransportV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
namespace QuantitativeMaass
variable {α H V ι κ τ : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- An actual isometric target contributes exactly its own canonical
packet energy, even when the ambient packet is not self-adjoint. -/
theorem isometric_target_energy (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ V)
    (J : V→ₗᵢ[ℂ]H) [J.toContinuousLinearMap.range.HasOrthogonalProjection]
    (B : H→L[ℂ]H) (T : V→L[ℂ]V) (hBT : ∀ x,B (J x)=J (T x))
    (hT : Summable (fun i => ‖T (c i)‖^2)) :
    hilbertSchmidtEnergy b (B.comp J.toContinuousLinearMap.range.starProjection)=
      hilbertSchmidtEnergy c T := by
  have he : B.comp J.toContinuousLinearMap=J.toContinuousLinearMap.comp T := by
    ext x
    exact hBT x
  rw [←isometric_cogram_projection J,←comp_assoc,he,comp_assoc]
  exact (isometry_extension_energy J c b T hT).2

/-- Counting with coefficient one on the canonical target and a finite-energy
column trace for the excess. The packet factorization is needed only on the
actual original source. No global Hilbert--Schmidt claim about the unrestricted
wave and no weight/wave commutation is used. -/
theorem metric_source_column_count [Countable ι]
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ V)
    (L : H≃L[ℂ]H) (B : H→L[ℂ]H) (T : V→L[ℂ]V)
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (J : V→ₗᵢ[ℂ]H) [J.toContinuousLinearMap.range.HasOrthogonalProjection]
    (hJU : ∀ x,J x∈U)
    (hBT : ∀ x,similarityOperator L B (J x)=J (T x))
    (v : τ→H) (hv : LinearIndependent ℂ v) (hU : ∀ i,L (v i)∈U)
    (a : τ→ℝ) (he : ∀ i,B (v i)=(a i:ℂ) • v i) (ha : ∀ i,1≤a i)
    (hB : Summable (fun i => ‖B (b i)‖^2)) (hT : Summable (fun i => ‖T (c i)‖^2))
    (μ : Measure α) (col : α→H) (hcol : MemLp col 2 μ)
    (C : Lp ℂ 2 μ→L[ℂ]H)
    (hfactor : ∀ x,L x∈U → B x=C (finiteEnergyColumnOperator μ col hcol x)) :
    Finite τ ∧ (Nat.card τ:ℝ)≤hilbertSchmidtEnergy c T+
      (‖L.toContinuousLinearMap‖^2*‖C‖^2)*columnLinearTrace μ col
        ((L.symm.toContinuousLinearMap.comp U.starProjection).comp L.symm.toContinuousLinearMap.adjoint-
          (L.symm.toContinuousLinearMap.comp J.toContinuousLinearMap.range.starProjection).comp
            L.symm.toContinuousLinearMap.adjoint) := by
  let W := J.toContinuousLinearMap.range
  have hWU : W≤U := by
    rintro _ ⟨x,rfl⟩
    exact hJU x
  obtain ⟨hf,hcount⟩ := similarity_count_nested_source b L B U W hWU v hv hU a he ha hB
  rw [isometric_target_energy b c J (similarityOperator L B) T hBT hT] at hcount
  have heq : hilbertSchmidtEnergy b
      (B.comp (L.symm.toContinuousLinearMap.comp (U.starProjection-W.starProjection)))=
      ∑' i,‖C (finiteEnergyColumnOperator μ col hcol
        (L.symm ((U.starProjection-W.starProjection) (b i))))‖^2 := by
    apply tsum_congr
    intro i
    change ‖B (L.symm ((U.starProjection-W.starProjection) (b i)))‖^2=_
    rw [hfactor]
    rw [L.apply_symm_apply]
    exact U.sub_mem (U.starProjection_apply_mem _) (hWU (W.starProjection_apply_mem _))
  rw [heq] at hcount
  have hbound := metric_column_excess_bound μ col hcol b L U W hWU C
  have hh := mul_le_mul_of_nonneg_left hbound (sq_nonneg ‖L.toContinuousLinearMap‖)
  have hresult := hcount.trans (add_le_add le_rfl hh)
  simpa only [mul_assoc] using And.intro hf hresult

#print axioms isometric_target_energy
#print axioms metric_source_column_count
end QuantitativeMaass
