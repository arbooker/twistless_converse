module

public import QuantitativeEulerEndpointNormalizedCombinedRegularV1
public import QuantitativeEulerEndpointBlockNormalizationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointBoundedTerminal
open QuantitativeEulerEndpointPrepared
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularCompactBranch AsymptoticRegularTrace
open QuantitativeEulerEndpointRegularBase QuantitativeEulerEndpointTerminalAlgebra
open QuantitativeEulerEndpointBlockNormalization QuantitativeSpectralSourceGram
open ContinuousLinearMap MeasureTheory

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))
variable (C : ℕ → ℝ)
  (hC : ∀ i x,‖normalizedCombinedRows A P e hs l i x‖≤C i)
local notation "r" => factor C (l.length+1)

def scaledRows (i : ℕ) (x : Base) : Space →L[ℂ] Space :=
  ((r : ℝ) : ℂ) • normalizedCombinedRows A P e hs l i x

theorem scaled_regular (i : ℕ) :
    (∀ g k,Measurable (fun x => matrix (scaledRows A P e hs l C i x) g k)) ∧
      Covariant (scaledRows A P e hs l C i) := by
  have hr := normalized_combined_rows_regular A P e hs l i
  exact ⟨matrix_smul_measurable _ _ hr.1,covariant_smul _ _ hr.2⟩

include hC in
theorem scaled_norm (i : ℕ) (x : Base) :
    ‖scaledRows A P e hs l C i x‖≤r*C i := by
  rw [scaledRows,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (factor_pos C (l.length+1))]
  exact mul_le_mul_of_nonneg_left (hC i x)
    (factor_pos C (l.length+1)).le

theorem scaled_source (i : ℕ) (x : Base) :
    scaledRows A P e hs l C i x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=
      scaledRows A P e hs l C i x := by
  rw [scaledRows,smul_mul_assoc,normalized_combined_rows_source]

def gram : Algebra A P := ∑ i : Fin (l.length+1),
  gramElement action_measurable (terminalRegion A P) (terminal_measurable A P)
    (scaledRows A P e hs l C i)
    (scaled_regular A P e hs l C i).1
    (scaled_regular A P e hs l C i).2
    (r*C i) (scaled_norm A P e hs l C hC i)
    (scaled_source A P e hs l C i)

theorem gram_nonneg : 0≤gram A P e hs l C hC :=
  Finset.sum_nonneg (fun _ _ => gramElement_nonneg _ _ _ _ _ _ _ _ _)

theorem gram_norm : ‖gram A P e hs l C hC‖≤1 := by
  apply (norm_sum_le _ _).trans
  exact (Finset.sum_le_sum (fun _ _ => gramElement_norm_le _ _ _ _ _ _ _ _ _)).trans
    (normalized_square_sum C (l.length+1))

theorem gram_order :
    0≤gram A P e hs l C hC ∧ gram A P e hs l C hC≤1 :=
  ⟨gram_nonneg A P e hs l C hC,
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (gram_nonneg A P e hs l C hC)).mp
      (gram_norm A P e hs l C hC)⟩

theorem rep_gram (x : Base) :
    rep A P (gram A P e hs l C hC) x=
      ∑ i : Fin (l.length+1),star (scaledRows A P e hs l C i x)*
        scaledRows A P e hs l C i x := by
  simp only [gram,map_sum,Finset.sum_apply]
  rfl

#print axioms scaled_regular
#print axioms scaled_norm
#print axioms gram_order
#print axioms rep_gram
end QuantitativeEulerEndpointBoundedTerminal
