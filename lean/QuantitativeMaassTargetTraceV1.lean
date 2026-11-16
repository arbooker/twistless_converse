module

public import QuantitativeMaassTargetMetricV1
public import QuantitativeMaassCuspidalBasisEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open scoped ENNReal

namespace QuantitativeMaass

variable {H V ι κ η : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The source-projected energy equals the sum over a basis of the source
subspace. Finiteness of that sum is proved, not assumed. -/
theorem source_energy_two_bases (W : Submodule ℂ H) [CompleteSpace W]
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ W) (B : H →L[ℂ] H)
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    Summable (fun j => ‖B (c j:H)‖^2) ∧
      hilbertSchmidtEnergy b (B.comp W.starProjection)=∑' j,‖B (c j:H)‖^2 := by
  have he : extendedHilbertEnergy b (B.comp W.starProjection)=
      ∑' j,ENNReal.ofReal (‖B (c j:H)‖^2) := by
    rw [←extendedHilbertEnergy_adjoint b (B.comp W.starProjection),
      ContinuousLinearMap.adjoint_comp,(isSelfAdjoint_starProjection W).adjoint_eq]
    change (∑' i,ENNReal.ofReal (‖W.starProjection (B.adjoint (b i))‖^2))=_
    rw [projected_energy_two_bases W b c,ContinuousLinearMap.adjoint_adjoint]
  have hs := projected_source_summable b W B hB
  have ht : (∑' j,ENNReal.ofReal (‖B (c j:H)‖^2))≠∞ := by
    rw [←he]
    exact hs.tsum_ofReal_lt_top.ne
  have hc : Summable (fun j => ‖B (c j:H)‖^2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal ht
  refine ⟨hc,?_⟩
  unfold extendedHilbertEnergy at he
  simp only [ContinuousLinearMap.comp_apply] at he
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs,
    ←ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hc] at he
  have hr := congrArg ENNReal.toReal he
  simpa only [hilbertSchmidtEnergy,ContinuousLinearMap.comp_apply,
    ENNReal.toReal_ofReal (tsum_nonneg (fun _ => sq_nonneg _))] using hr

/-- Under the constructed metric, the exact target contribution is the
canonical spectral energy. No constant is placed in front of that term. -/
theorem targetMetric_energy (W : Submodule ℂ H) [CompleteSpace W]
    (J : V ≃L[ℂ] W) {a : ℝ} (ha : 0<a) (hJ : ∀ x,a*‖x‖^2≤‖J x‖^2)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ V)
    (B : H →L[ℂ] H) (D : V →L[ℂ] V)
    (hBD : ∀ x,B (J x:H)=(J (D x):H))
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    Summable (fun j => ‖D (c j)‖^2) ∧
      hilbertSchmidtEnergy b
        ((similarityOperator (targetMetric W J ha hJ) B).comp W.starProjection)=
      hilbertSchmidtEnergy c D := by
  let U := normalizedTargetEquiv J ha hJ
  let d : HilbertBasis κ ℂ W := HilbertBasis.ofRepr (U.symm.trans c.repr)
  let L := targetMetric W J ha hJ
  have hd (j : κ) : d j=U (c j) := rfl
  have hL (x : V) : L (J x:H)=(U x:H) := targetMetric_embedded W J ha hJ x
  have hLi (x : V) : L.symm (U x:H)=(J x:H) := by
    rw [←hL,L.symm_apply_apply]
  have hact (j : κ) : similarityOperator L B (d j:H)=(U (D (c j)):H) := by
    rw [hd]
    change L (B (L.symm (U (c j):H)))=_
    rw [hLi,hBD,hL]
  have hn (j : κ) : ‖similarityOperator L B (d j:H)‖^2=‖D (c j)‖^2 := by
    rw [hact]
    exact congrArg (fun r : ℝ => r^2) (U.norm_map (D (c j)))
  have hs := source_energy_two_bases W b d (similarityOperator L B)
    (similarityOperator_summable b L B hB)
  simp_rw [hn] at hs
  exact hs

/-- The abstract target--excess counting lemma with its metric explicitly
constructed from the bounded target embedding. The geometric application
must still prove that embedding, the intertwining identity and the excess
estimate for its actual operators. -/
theorem count_target_canonical_excess (W : Submodule ℂ H) [CompleteSpace W]
    (J : V ≃L[ℂ] W) {a : ℝ} (ha : 0<a) (hJ : ∀ x,a*‖x‖^2≤‖J x‖^2)
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ V)
    (B : H →L[ℂ] H) (D : V →L[ℂ] V)
    (hBD : ∀ x,B (J x:H)=(J (D x):H))
    (v : η → H) (hv : LinearIndependent ℂ v) (h : η → ℝ)
    (he : ∀ i,B (v i)=(h i:ℂ) • v i) (hl : ∀ i,1≤h i)
    (hB : Summable (fun i => ‖B (b i)‖^2)) :
    Finite η ∧ (Nat.card η:ℝ)≤hilbertSchmidtEnergy c D+
      ‖(targetMetric W J ha hJ).toContinuousLinearMap‖^2 *
        hilbertSchmidtEnergy b (B.comp Wᗮ.starProjection) := by
  have hc := similarity_count_target_excess b (targetMetric W J ha hJ) B W
    (targetMetric_symm_perp W J ha hJ) v hv h he hl hB
  rw [(targetMetric_energy W J ha hJ b c B D hBD hB).2] at hc
  exact hc

#print axioms source_energy_two_bases
#print axioms targetMetric_energy
#print axioms count_target_canonical_excess

end QuantitativeMaass
