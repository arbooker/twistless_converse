module

public import QuantitativeHolomorphicRegularClosureV1
public import AsymptoticRegularTraceSandwichV1
public import AsymptoticRegularInverseV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCompactObservationCount AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open scoped ENNReal

private theorem extended_isometry_gram {G H K : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : G →L[ℂ] H) (S : G →L[ℂ] K) (hU : U.adjoint.comp U = 1) :
    (U.comp S.adjoint).adjoint.comp (U.comp S.adjoint) = S.comp S.adjoint := by
  rw [adjoint_comp,adjoint_adjoint,comp_assoc,← comp_assoc U.adjoint U,hU]
  simp only [one_def,id_comp]

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

/-- The exact ambient normalization is a partial isometry with the actual
terminal strip as initial projection. -/
theorem normalizedRegularAmbientCountReconstruction_gram (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) :
    (normalizedRegularAmbientCountReconstruction A hN P e z).adjoint.comp
      (normalizedRegularAmbientCountReconstruction A hN P e z) =
      AsymptoticOrbitDiagonal.corner
        (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z := by
  let U := normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)
  have hU : U.adjoint.comp U = 1 := (norm_map_iff_adjoint_comp_self U).mp
    (normalizedRegularCountReconstruction_norm A hN P e z)
  exact (extended_isometry_gram U
    (AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z).subtypeL hU).trans
    (AsymptoticOrbitRegion.subtype_comp_adjoint
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) z)

theorem normalizedRegularAmbientCountReconstruction_norm_le (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) :
    ‖normalizedRegularAmbientCountReconstruction A hN P e z‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  change ‖normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)
    ((AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint v)‖ ≤ 1*‖v‖
  have he := normalizedRegularCountReconstruction_norm A hN P e z
    ((AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint v)
  apply he.trans_le
  simpa only [one_mul,Submodule.adjoint_subtypeL] using
    (AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z).norm_orthogonalProjectionOnto_apply_le v

/-- The normalized ambient reconstruction has exactly the terminal area's
finite regular squared norm, independent of the orbit root or sector. -/
theorem normalizedRegularAmbientCountReconstruction_trace_gram (hN : 0 < N) (P : Parameters A)
    (e : Sector N) :
    AsymptoticRegularTrace.trace volume (fun z =>
      (normalizedRegularAmbientCountReconstruction A hN P e z).adjoint.comp
        (normalizedRegularAmbientCountReconstruction A hN P e z)) =
      ENNReal.ofReal (AsymptoticReconstructedCount.parameters A P).ε⁻¹ := by
  simp only [normalizedRegularAmbientCountReconstruction_gram]
  rw [AsymptoticOrbitDiagonal.trace_corner _
    (AsymptoticCertificateOperators.highStrip_measurable _)]
  exact AsymptoticHyperbolicArea.closed_terminal_area
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos

/-- Finite observation Gram polynomials preserve regularity. This algebraic
lemma does not assume any spectral estimate. -/
theorem finiteRowFilter_regular (qs : Finset ι)
    (L : ι → UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace) (b : ι → ℝ)
    (V : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace)
    (hmL : ∀ i g h, Measurable (fun z => matrix (L i z) g h))
    (hcL : ∀ i, Covariant (L i))
    (hmV : ∀ g h, Measurable (fun z => matrix (V z) g h)) (hcV : Covariant V) (d : ℕ) :
    (∀ g h, Measurable (fun z => matrix (finiteRowFilter qs (fun i => L i z) b (V z) d) g h)) ∧
    Covariant (fun z => finiteRowFilter qs (fun i => L i z) b (V z) d) := by
  let G := fun z => finiteRowGram qs (fun i => L i z) (V z)
  have hmG : ∀ g h, Measurable (fun z => matrix (G z) g h) := by
    apply matrix_finsetSum_measurable
    intro i _
    have hr := matrix_comp_measurable (L i) V (hmL i) hmV
    exact matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hr) hr
  have hcG : Covariant G := by
    apply covariant_finsetSum
    intro i _
    have hr := covariant_comp (L i) V (hcL i) hcV
    exact covariant_comp _ _ (covariant_adjoint _ hr) hr
  have hmS := matrix_sub_measurable (fun _ => (1 : RegularSpace →L[ℂ] RegularSpace))
    (fun z => (((finiteRowBound qs b)⁻¹ : ℝ) : ℂ) • G z) (fun _ _ => measurable_const)
    (matrix_smul_measurable _ G hmG)
  have hcS := covariant_sub (fun _ => (1 : RegularSpace →L[ℂ] RegularSpace))
    (fun z => (((finiteRowBound qs b)⁻¹ : ℝ) : ℂ) • G z) covariant_one (covariant_smul _ G hcG)
  have he (z : UpperHalfPlane) :
      1 - (((finiteRowBound qs b)⁻¹ : ℝ) : ℂ) • G z =
      1 - (finiteRowBound qs b)⁻¹ • G z := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (finiteRowBound qs b)⁻¹ (G z)]
    rfl
  have hh : (fun z => (1 - (((finiteRowBound qs b)⁻¹ : ℝ) : ℂ) • G z)^d) =
      fun z => finiteRowFilter qs (fun i => L i z) b (V z) d := by
    funext z
    exact congrArg (fun T : RegularSpace →L[ℂ] RegularSpace => T^d) (he z)
  exact (congrArg (fun W : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace =>
    (∀ g h, Measurable (fun z => matrix (W z) g h)) ∧ Covariant W) hh).mp
      ⟨matrix_pow_measurable _ hmS d,covariant_pow _ hcS d⟩

def regularSourceFilter (hN : 0 < N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) (z : UpperHalfPlane) :=
  finiteRowFilter qs
    (fun i => AsymptoticRegularObservationRows.row hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z)
    (fun i => rowBound hN (r i) (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4))
    (normalizedRegularAmbientCountReconstruction A hN P e z) d

theorem regularSourceFilter_regular (hN : 0 < N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) :
    (∀ g h, Measurable (fun z => matrix (regularSourceFilter A hN P e qs r s hs d z) g h)) ∧
    Covariant (regularSourceFilter A hN P e qs r s hs d) := by
  let rows := fun i => rowExpression hN (r i) e (hs i)
    (AsymptoticReconstructedCount.parameters A P).epsilon_pos
    ((AsymptoticReconstructedCount.parameters A P).s+4)
  have he (i : ι) : regularSum (rows i) = fun z =>
      AsymptoticRegularObservationRows.row hN (r i) e (hs i)
        (AsymptoticReconstructedCount.parameters A P).epsilon_pos
        ((AsymptoticReconstructedCount.parameters A P).s+4) z :=
    funext (fun z => regularSum_rowExpression hN (r i) e (hs i) _ _ z)
  apply finiteRowFilter_regular
  · intro i
    exact (congrArg (fun W : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace =>
      ∀ g h, Measurable (fun z => matrix (W z) g h)) (he i)).mp
        (regularSum_matrix_measurable (rows i))
  · intro i
    exact (congrArg Covariant (he i)).mp (regularSum_covariant (rows i))
  · exact (normalizedRegularCountReconstruction_regular A hN P e).1
  · exact (normalizedRegularCountReconstruction_regular A hN P e).2

theorem regularSourceFilter_norm_le (hN : 0 < N) (P : Parameters A) (e : Sector N)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) (z : UpperHalfPlane) :
    ‖regularSourceFilter A hN P e qs r s hs d z‖ ≤ 1 :=
  (finiteRowFilter_order qs _ _
    (fun i => regular_row_norm_le_physical_bound hN (r i) e (hs i)
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) z) _
    (normalizedRegularAmbientCountReconstruction_norm_le A hN P e z) d).2.2

#print axioms normalizedRegularAmbientCountReconstruction_gram
#print axioms normalizedRegularAmbientCountReconstruction_norm_le
#print axioms normalizedRegularAmbientCountReconstruction_trace_gram
#print axioms regularSourceFilter_regular

end QuantitativeHolomorphic
