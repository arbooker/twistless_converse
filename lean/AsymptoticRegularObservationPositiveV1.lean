module

public import AsymptoticRegularObservationRowsV1
public import AsymptoticRegularIncludedReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace InnerProductSpace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction
open scoped InnerProduct ENNReal

variable {ι : Type*} [Fintype ι]

noncomputable def observations {N : ℕ} (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (e : Sector N) (z : ℍ) : Space →L[ℂ] PiLp 2 (fun _ : ι => Space) :=
  AsymptoticObservationStack.stack (fun i => AsymptoticRegularObservationRows.row hN (r i) e (hs i) hε t z)

theorem observations_norm_le {N : ℕ} (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (e : Sector N) (z : ℍ) :
    ‖observations hN r s hs hε t e z‖≤
      ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Space)).symm.toContinuousLinearMap‖*
        ∑ i,AsymptoticRegularObservationRows.rowBound hN (r i) (hs i) hε t :=
  AsymptoticObservationStack.stack_norm_le _ _
    (fun i => AsymptoticRegularObservationRows.rowBound_nonneg hN (r i) (hs i) hε t)
    (fun i => AsymptoticRegularObservationRows.row_norm_le hN (r i) e (hs i) hε t z)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The actual finite-observation positive operator in the regular
counting realization. The same common parameters occur in the
holomorphic count-to-trace theorem; no contraction hypothesis remains. -/
noncomputable def positive (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) : Space →L[ℂ] Space :=
  let P' := AsymptoticReconstructedCount.parameters A P
  AsymptoticObservation.operator (includedExtension A hN P' (multiplier e) z)
    (observations hN r s hs P'.epsilon_pos (P'.s+4) e z)
    (includedExtension_norm_ge A hN P' (multiplier e) z
      (lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)))

theorem positive_isPositive (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    (positive A hN P r s hs e z).IsPositive :=
  AsymptoticObservation.operator_positive _ _ _

theorem positive_norm_le_one (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    ‖positive A hN P r s hs e z‖≤1 :=
  AsymptoticObservation.operator_norm_le_one _ _ _

/-- A reconstructed counting vector is fixed whenever each literal
compact observation row vanishes on it. -/
theorem positive_fixes (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ)
    (g : TerminalSpace A (AsymptoticReconstructedCount.parameters A P) z)
    (hg : ∀ i,AsymptoticRegularObservationRows.row hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z
      (includedExtension A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z g)=0) :
    positive A hN P r s hs e z
      (includedExtension A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z g)=
      includedExtension A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z g :=
  AsymptoticObservation.operator_fixes _ _ _ ((AsymptoticObservationStack.stack_eq_zero_iff _ _).mpr hg)

theorem includedExtension_eq_full_comp (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ) :
    includedExtension A hN P χ z=
      (includedFull A hN P χ z).comp (TerminalSpace A P z).subtypeL := by
  apply ContinuousLinearMap.ext
  intro g
  have hg : AsymptoticOrbitRegion.restrict (AsymptoticCertificateOperators.highStrip P.ε) z (g:Space)=g := by
    apply Subtype.ext
    exact (AsymptoticOrbitRegion.mem_space _ _ _).mp g.property
  change AsymptoticRegularInclusion.inclusion P.epsilon_pos z (extension A hN P χ z g)=
    AsymptoticRegularInclusion.inclusion P.epsilon_pos z (full A hN P χ z (g:Space))
  rw [full_eq_extension,hg]

theorem includedExtension_adjoint_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (z : ℍ) (x : Space) :
    ‖(includedExtension A hN P χ z).adjoint x‖≤‖(includedFull A hN P χ z).adjoint x‖ := by
  have he := congrArg (fun T : TerminalSpace A P z →L[ℂ] Space => T.adjoint x)
    (includedExtension_eq_full_comp A hN P χ z)
  simp only [adjoint_comp,comp_apply] at he
  have hn : ‖(TerminalSpace A P z).subtypeL.adjoint‖≤1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact terminal_inclusion_norm_le A P z
  apply (le_of_eq (congrArg norm he)).trans
  simpa only [one_mul] using ((TerminalSpace A P z).subtypeL.adjoint).le_of_opNorm_le hn
    ((includedFull A hN P χ z).adjoint x)

theorem positive_re_inner_le_full_gram (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) (x : Space) :
    (⟪positive A hN P r s hs e z x,x⟫_ℂ).re≤
      ‖(includedFull A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z).adjoint x‖^2 := by
  apply (AsymptoticObservation.operator_re_inner_le_gram _ _ _ x).trans
  exact pow_le_pow_left₀ (norm_nonneg _) (includedExtension_adjoint_norm_le A hN _ _ z x) 2

set_option maxHeartbeats 800000 in
/-- Finite rooted mass for each actual regular observation operator.
This is a pointwise domination argument; measurability and covariance of
the inverse family are separate obligations for trace comparison. -/
theorem positive_trace_finite (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) :
    trace volume (positive A hN P r s hs e)<∞ := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hb := includedFull_range_gram_trace_finite A hN P' (multiplier e)
    (fun q _ => multiplier_norm e q)
    (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q))
  apply lt_of_le_of_lt (b:=trace volume (fun z =>
    (includedFull A hN P' (multiplier e) z).comp
      (includedFull A hN P' (multiplier e) z).adjoint)) _ hb
  change (∫⁻ z,ENNReal.ofReal (matrix (positive A hN P r s hs e z) 1 1).re ∂volume)≤
    ∫⁻ z,ENNReal.ofReal (matrix ((includedFull A hN P' (multiplier e) z).comp
      (includedFull A hN P' (multiplier e) z).adjoint) 1 1).re ∂volume
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  have hg := matrix_gram (includedFull A hN P' (multiplier e) z).adjoint 1
  rw [adjoint_adjoint] at hg
  have hl : (matrix (positive A hN P r s hs e z) 1 1).re=
      (⟪positive A hN P r s hs e z (delta 1),delta 1⟫_ℂ).re := by
    calc
      _ = (⟪delta 1,positive A hN P r s hs e z (delta 1)⟫_ℂ).re :=
        congrArg Complex.re (delta_inner 1 (positive A hN P r s hs e z (delta 1))).symm
      _ = _ := inner_re_symm (𝕜:=ℂ) _ _
  exact hl.le.trans ((positive_re_inner_le_full_gram A hN P r s hs e z (delta 1)).trans_eq hg.symm)

#print axioms observations_norm_le
#print axioms positive_isPositive
#print axioms positive_norm_le_one
#print axioms positive_fixes
#print axioms includedExtension_eq_full_comp
#print axioms includedExtension_adjoint_norm_le
#print axioms positive_re_inner_le_full_gram
#print axioms positive_trace_finite

end AsymptoticRegularObservation
