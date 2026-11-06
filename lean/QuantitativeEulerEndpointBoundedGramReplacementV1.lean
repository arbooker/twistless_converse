module

public import QuantitativeEulerEndpointBoundedActualDataV1
public import QuantitativeEulerEndpointCommonReconstructionV1
public import QuantitativeHolomorphicFilterStabilityV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open AsymptoticRegularCompactBranch ContinuousLinearMap
open QuantitativeEulerEndpointBlockNormalization QuantitativeEulerEndpointTerminalAlgebra

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))

/-- The actual packet before applying normalized reconstruction. -/
def uncomposedCombinedRows : ℕ → UpperHalfPlane → Space →L[ℂ] Space
  | 0,x => newBaselineDetector N e hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) x
  | j+1,x => packetSequence N (NeZero.pos N) (sign e.1) hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      ((AsymptoticReconstructedCount.parameters A P).s+4) l j x

theorem combined_rows_comp (i : ℕ) (x : UpperHalfPlane) :
    normalizedCombinedRows A P e hs l i x=uncomposedCombinedRows A P e hs l i x*
      normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x := by
  cases i <;> rfl

theorem uncomposed_combined_rows_wide_norm {R Y H : ℝ} (hY : 0<Y)
    (hre : ∀ z∈s,|z.re|≤R) (hlo : ∀ z∈s,Y≤z.im) (hhi : ∀ z∈s,z.im≤H)
    (i : ℕ) (x : UpperHalfPlane) :
    ‖uncomposedCombinedRows A P e hs l i x‖≤wideCombinedBound A P e R Y H l i := by
  cases i with
  | zero =>
    exact newBaselineDetector_wide_norm hs (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      hY hre hlo hhi N e ((AsymptoticReconstructedCount.parameters A P).s+4) x
  | succ i =>
    exact packet_sequence_wide_norm N (NeZero.pos N) (sign e.1) hs
      (AsymptoticReconstructedCount.parameters A P).epsilon_pos hY hre hlo hhi
      ((AsymptoticReconstructedCount.parameters A P).s+4) l i x

/-- Reconstruction may be replaced while keeping exactly the coefficients
and original observation rows of the actual bounded Gram. -/
def replacementGram (C : ℕ → ℝ) (x : UpperHalfPlane) (U : Space →L[ℂ] Space) :=
  finiteRowGram Finset.univ (fun i : Fin (l.length+1) =>
    ((factor C (l.length+1):ℝ):ℂ) • uncomposedCombinedRows A P e hs l i x) U

theorem replacementGram_exact (C : ℕ → ℝ)
    (hC : ∀ i x,‖normalizedCombinedRows A P e hs l i x‖≤C i) (x : UpperHalfPlane) :
    rep A P (QuantitativeEulerEndpointBoundedTerminal.gram A P e hs l C hC) x=
      replacementGram A P e hs l C x (normalizedRegularAmbientCountReconstruction A (NeZero.pos N) P e x) := by
  rw [QuantitativeEulerEndpointBoundedTerminal.rep_gram]
  unfold replacementGram finiteRowGram
  apply Finset.sum_congr rfl
  intro i _
  rw [QuantitativeEulerEndpointBoundedTerminal.scaledRows,combined_rows_comp]
  rw [smul_comp]
  rfl

theorem replacementGram_difference (C : ℕ → ℝ) (x : UpperHalfPlane)
    (hC : ∀ i,‖uncomposedCombinedRows A P e hs l i x‖≤C i)
    (U V : Space →L[ℂ] Space) (hU : ‖U‖≤1) (hV : ‖V‖≤1) :
    ‖replacementGram A P e hs l C x V-replacementGram A P e hs l C x U‖≤2*‖V-U‖ := by
  let r := factor C (l.length+1)
  have hrows (i : Fin (l.length+1)) : ‖(r:ℂ) • uncomposedCombinedRows A P e hs l i x‖≤r*C i := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (factor_pos C (l.length+1))]
    exact mul_le_mul_of_nonneg_left (hC i) (factor_pos C (l.length+1)).le
  have hh := finiteRowGram_difference Finset.univ
    (fun i : Fin (l.length+1) => (r:ℂ) • uncomposedCombinedRows A P e hs l i x)
    (fun i => r*C i) hrows U V hU hV
  have hs := normalized_square_sum C (l.length+1)
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hs (norm_nonneg (V-U))])

theorem replacementGram_order (C : ℕ → ℝ) (x : UpperHalfPlane)
    (hC : ∀ i,‖uncomposedCombinedRows A P e hs l i x‖≤C i)
    (U : Space →L[ℂ] Space) (hU : ‖U‖≤1) :
    0≤replacementGram A P e hs l C x U ∧ replacementGram A P e hs l C x U≤1 := by
  let r := factor C (l.length+1)
  let B := fun i : Fin (l.length+1) => ((r:ℂ) • uncomposedCombinedRows A P e hs l i x).comp U
  have hrows (i : Fin (l.length+1)) : ‖B i‖≤r*C i := by
    apply (opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_left hU (norm_nonneg _)).trans
    rw [mul_one,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (factor_pos C (l.length+1))]
    exact mul_le_mul_of_nonneg_left (hC i) (factor_pos C (l.length+1)).le
  have hpos : 0≤replacementGram A P e hs l C x U := by
    change 0≤∑ i : Fin (l.length+1),star (B i)*B i
    exact Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _)
  have hn : ‖replacementGram A P e hs l C x U‖≤1 := by
    change ‖∑ i : Fin (l.length+1),(B i).adjoint.comp (B i)‖≤1
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i (_hi : i∈Finset.univ) => ?_)).trans (normalized_square_sum C (l.length+1))
    have hp : ‖(B i).adjoint.comp (B i)‖≤‖B i‖^2 := by
      simpa only [adjoint.norm_map,pow_two] using opNorm_comp_le (B i).adjoint (B i)
    exact hp.trans (pow_le_pow_left₀ (norm_nonneg _) (hrows i) 2)
  exact ⟨hpos,(CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mp hn⟩

#print axioms uncomposed_combined_rows_wide_norm
#print axioms replacementGram_exact
#print axioms replacementGram_difference
#print axioms replacementGram_order
end QuantitativeEulerEndpointPrepared
