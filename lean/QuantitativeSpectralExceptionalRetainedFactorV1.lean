module

public import QuantitativeSpectralExceptionalWordResidualsV1
public import QuantitativeSpectralExceptionalWideSamplingV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open MeasureTheory UpperHalfPlane ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticRegularBranchFamily AsymptoticObservationStack AsymptoticOrbitDiagonal
open AsymptoticCongruenceLabels
open QuantitativeSpectralExceptionalRows
open QuantitativeSpectralExceptionalUnweight (G Space)
open QuantitativeSpectralObservability QuantitativeSpectralObservabilityDecoded
open scoped lp MatrixGroups ENNReal

attribute [local instance] Classical.propDecidable

theorem pull_matrix (a g h : G) : matrix (pull a) g h = if a*g=h then 1 else 0 := by
  by_cases he : a*g=h
  · simp [matrix, pull_apply, delta, he]
  · simp [matrix, pull_apply, delta, he]

theorem pull_covariant (a : G) : Covariant (fun _ : ℍ => pull a) := by
  intro x k g h
  simp only [pull_matrix]
  have he : a*(g*k)=h*k ↔ a*g=h := by rw [← mul_assoc]; exact mul_right_cancel_iff
  simp only [he]

variable {ι : Type*} [Fintype ι]

theorem reducedFamily_regular (N : ℕ) (hN : 0 < N) (H : ℝ) (b : ι → Branch)
    (γ : ι → SL(2,ℤ)) (c : ι → ℂ) {ε : ℝ} (hε : 0 < ε) (t : ℕ) :
    (∀ g h, Measurable (fun x => matrix (reducedFamily N hN H b γ c hε t x) g h)) ∧
      Covariant (reducedFamily N hN H b γ c hε t) := by
  have hs := sampling_regular N hN H hε t
  constructor
  · exact matrix_finsetSum_measurable _ _ (fun i _ => matrix_smul_measurable _ _
      (matrix_comp_measurable _ _ (fun _ _ => measurable_const) hs.1))
  · exact covariant_finsetSum _ _ (fun i _ => covariant_smul _ _
      (covariant_comp _ _ (pull_covariant _) hs.2))

theorem reducedFamily_norm (N : ℕ) (hN : 0 < N) (H : ℝ) (b : ι → Branch)
    (γ : ι → SL(2,ℤ)) (c : ι → ℂ) {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) :
    ‖reducedFamily N hN H b γ c hε t x‖ ≤
      (∑ i, ‖c i‖) *
        (QuantitativeSpectralObservabilitySampling.samplingBound N hN H ε t *
          bound AsymptoticFreshCompactDefects.identityBranch (wideCompactCover_compact N hN H) hε t) := by
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hp := (opNorm_comp_le (pull (integralLabel (γ i) * label (b i))) (sampling N hN H hε t x)).trans
    (mul_le_mul_of_nonneg_right (pull_norm _) (norm_nonneg _))
  have hp' : ‖(pull (integralLabel (γ i) * label (b i))).comp (sampling N hN H hε t x)‖ ≤
      ‖sampling N hN H hε t x‖ := by simpa only [one_mul] using hp
  exact hp'.trans (sampling_norm N hN H hε t x)

/-- Restricting the retained outputs of a compact row is exactly
restriction to its source region minus the exceptional geometric set. -/
theorem retained_source_eq (s e : Set ℍ) (T : ℍ → Space →L[ℂ] Space) (x : ℍ) :
    retained e (fun y => (corner s y).comp (T y)) x = (corner (s \ e) x).comp (T x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext g
  simp only [retained, comp_apply, corner_apply, Set.mem_compl_iff, Set.mem_sdiff]
  by_cases hs : g • x ∈ s <;> by_cases he : g • x ∈ e <;> simp [hs,he]

/-- The actual compact reduced row factors into the explicitly bounded
residual recombination plus an actual cusp-supported error. This proves
the operator identity from branch formulas; only reduction geometry is
left as input. -/
theorem compact_row_factorization (N : ℕ) (hN : 0 < N) (H C : ℝ)
    (b : ι → Branch) (γ : ι → SL(2,ℤ)) (c : ι → ℂ)
    {s : Set ℍ} (hs : IsCompact s)
    (hred : ∀ i z, z ∈ s \ wideTailCover N (H/C) →
      (integralLabel (γ i) * label (b i)) • z ∈ wideCompactCover N H)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    (corner s x).comp (reducedFamily N hN H b γ c hε t x) =
      ((corner (s \ wideTailCover N (H/C)) x).comp (recombine b c hε t Ds Db x)).comp
        (stack (residualRows b γ c hs hε t x)) +
      omitted (wideTailCover N (H/C))
        (fun y => (corner s y).comp (reducedFamily N hN H b γ c hε t y)) x := by
  have hsplit := retained_add_omitted (wideTailCover N (H/C))
    (fun y => (corner s y).comp (reducedFamily N hN H b γ c hε t y)) x
  rw [retained_source_eq] at hsplit
  rw [retained_residual_factorization N hN H b γ c hs (fun _ hz => hz.1) hred hε t Ds Db x] at hsplit
  exact hsplit.symm

/-- The exceptional operator occurring in `compact_row_factorization`
has genuine regular polar rank at most 3*index*C/H. -/
theorem compact_row_error_rank (N : ℕ) (hN : 0 < N) {H C : ℝ} (hH : 0 < H) (hC : 0 < C)
    (b : ι → Branch) (γ : ι → SL(2,ℤ)) (c : ι → ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (t : ℕ) :
    trace volume (fun x => (omitted (wideTailCover N (H/C))
      (fun y => (corner s y).comp (reducedFamily N hN H b γ c hε t y)) x).kerᗮ.starProjection) ≤
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N) : ℝ≥0∞) *
        (3 * ENNReal.ofReal (C/H)) := by
  have hr := reducedFamily_regular N hN H b γ c hε t
  have hm := matrix_comp_measurable (corner (G := G) s) _
    (corner_matrix_measurable (fun g => (AsymptoticRationalGroup.measurePreserving g).measurable)
      hs.measurableSet) hr.1
  have hc := covariant_comp (corner (G := G) s) _ (corner_covariant s) hr.2
  have hb (x : ℍ) : ‖(corner s x).comp (reducedFamily N hN H b γ c hε t x)‖ ≤
      (∑ i, ‖c i‖) *
        (QuantitativeSpectralObservabilitySampling.samplingBound N hN H ε t *
          bound AsymptoticFreshCompactDefects.identityBranch (wideCompactCover_compact N hN H) hε t) :=
    (omitted_norm_le s _ x).trans (reducedFamily_norm N hN H b γ c hε t x)
  have hh := omitted_rank_le_area volume AsymptoticRationalGroup.measurePreserving
    (wideTailCover_measurable N hN (H/C)) _ hm hc _ hb
  apply hh.trans
  simpa only [inv_div] using wideTailCover_area N hN (div_pos hH hC)

#print axioms reducedFamily_regular
#print axioms compact_row_factorization
#print axioms compact_row_error_rank

end QuantitativeSpectralExceptionalReducedRows
