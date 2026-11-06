module

public import QuantitativeSpectralExceptionalResidualFamilyV1
public import AsymptoticObservationStackV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open MeasureTheory UpperHalfPlane ContinuousLinearMap AsymptoticObservationStack
open AsymptoticRegularBranchFamily AsymptoticCongruenceLabels
open QuantitativeSpectralExceptionalUnweight (G Space)
open QuantitativeSpectralObservability
open scoped lp MatrixGroups

variable {ι : Type*} [Fintype ι]

/-- The actual finite residual stack: its first row is the original
rational relation, and the remaining rows are the reducing modular defects. -/
def residualRows (b : ι → Branch) (γ : ι → SL(2,ℤ)) (c : ι → ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) :
    Option ι → Space →L[ℂ] Space
  | none => family b c hs hε t x
  | some i => AsymptoticCongruenceDefect.operator (γ i) (image_compact (b i) hs) hε t x

/-- Explicit bounded recombination of the original residual and actual
modular-defect rows; this operator is constructed, not postulated. -/
def recombine (b : ι → Branch) (c : ι → ℂ) {s : Set ℍ} {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    PiLp 2 (fun _ : Option ι => Space) →L[ℂ] Space :=
  (QuantitativeSpectralExceptionalUnweight.unweight hε t Ds x).comp
      (PiLp.proj 2 (fun _ : Option ι => Space) none) +
    ∑ i, c i • (pull (label (b i))).comp
      ((QuantitativeSpectralExceptionalUnweight.unweight hε t (Db i) x).comp
        (PiLp.proj 2 (fun _ : Option ι => Space) (some i)))

theorem recombine_apply (b : ι → Branch) (c : ι → ℂ) {s : Set ℍ} {ε : ℝ}
    (hε : 0 < ε) (t : ℕ) (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t)
    (x : ℍ) (v : PiLp 2 (fun _ : Option ι => Space)) :
    recombine b c hε t Ds Db x v =
      QuantitativeSpectralExceptionalUnweight.unweight hε t Ds x (v none) +
        ∑ i, c i • pull (label (b i)) (QuantitativeSpectralExceptionalUnweight.unweight hε t (Db i) x (v (some i))) := by
  simp only [recombine, _root_.add_apply, _root_.sum_apply, smul_apply, comp_apply, PiLp.proj_apply]

/-- The recombination cost depends on inverse caps and fixed scalar
coefficients, not on the size of the residuals or any assumed factorization. -/
theorem recombine_norm (b : ι → Branch) (c : ι → ℂ) {s : Set ℍ} {ε : ℝ}
    (hε : 0 < ε) (t : ℕ) (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    ‖recombine b c hε t Ds Db x‖ ≤ Ds.bound + ∑ i, ‖c i‖ * (Db i).bound := by
  apply opNorm_le_bound _ (add_nonneg Ds.bound_nonneg
    (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (Db i).bound_nonneg)))
  intro v
  rw [recombine_apply, add_mul, Finset.sum_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact ((QuantitativeSpectralExceptionalUnweight.unweight hε t Ds x).le_of_opNorm_le
      (QuantitativeSpectralExceptionalUnweight.unweight_norm hε t Ds x) _).trans
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v none) Ds.bound_nonneg)
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul]
    have hp := (pull (label (b i))).le_of_opNorm_le (pull_norm _)
      (QuantitativeSpectralExceptionalUnweight.unweight hε t (Db i) x (v (some i)))
    simp only [one_mul] at hp
    have hu := (QuantitativeSpectralExceptionalUnweight.unweight hε t (Db i) x).le_of_opNorm_le
      (QuantitativeSpectralExceptionalUnweight.unweight_norm hε t (Db i) x) (v (some i))
    have hb := (hp.trans hu).trans (mul_le_mul_of_nonneg_left
      (PiLp.norm_apply_le v (some i)) (Db i).bound_nonneg)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (norm_nonneg (c i))

theorem recombine_stack (b : ι → Branch) (γ : ι → SL(2,ℤ)) (c : ι → ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    (recombine b c hε t Ds Db x).comp (stack (residualRows b γ c hs hε t x)) =
      (QuantitativeSpectralExceptionalUnweight.unweight hε t Ds x).comp (family b c hs hε t x) +
        correctionFamily b γ c hs hε t Db x := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [comp_apply, recombine_apply, stack_apply, residualRows, _root_.add_apply,
    correctionFamily, _root_.sum_apply, smul_apply, correction, comp_apply]

/-- The retained sampled rational row factors through a concrete finite
stack of initial and modular residuals, with the explicitly bounded map
`recombine`. The only premises are geometric reduction and cap bounds. -/
theorem retained_residual_factorization (N : ℕ) (hN : 0 < N) (H : ℝ)
    (b : ι → Branch) (γ : ι → SL(2,ℤ)) (c : ι → ℂ)
    {s E : Set ℍ} (hs : IsCompact s) (hEs : E ⊆ s)
    (hred : ∀ i z, z ∈ E → (integralLabel (γ i) * label (b i)) • z ∈ wideCompactCover N H)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner E x).comp (reducedFamily N hN H b γ c hε t x) =
      ((AsymptoticOrbitDiagonal.corner E x).comp (recombine b c hε t Ds Db x)).comp
        (stack (residualRows b γ c hs hε t x)) := by
  rw [comp_assoc, recombine_stack]
  exact retained_family_identity N hN H b γ c hs hEs hred hε t Ds Db x

#print axioms recombine_norm
#print axioms recombine_stack
#print axioms retained_residual_factorization

end QuantitativeSpectralExceptionalReducedRows
