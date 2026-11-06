module

public import QuantitativeSpectralExceptionalGeneratorWordV1
public import QuantitativeSpectralExceptionalFundamentalRowsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane ContinuousLinearMap AsymptoticObservationStack AsymptoticRegularBranchFamily
open AsymptoticOrbitDiagonal QuantitativeSpectralWordDefect
open QuantitativeSpectralExceptionalUnweight (G Space)
open QuantitativeSpectralObservability
open scoped MatrixGroups lp

variable {ι : Type*} [Fintype ι]

/-- Explicit recombination from the original rational relation and the
single fixed signed-generator stack. Word transport is constructed above. -/
def generatorRecombine (A : Finset SL(2,ℤ)) (b : ι → Branch)
    (w : ι → List SL(2,ℤ)) (hw : ∀ i a, a ∈ w i → a ∈ A) (c : ι → ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    GeneratorData A →L[ℂ] Space :=
  (QuantitativeSpectralExceptionalUnweight.unweight hε t Ds x).comp
      (PiLp.proj 2 (fun _ : Option ↥A => Space) none) +
    ∑ i, c i • (pull (label (b i))).comp
      ((QuantitativeSpectralExceptionalUnweight.unweight hε t (Db i) x).comp
        (wordRecombine A (image_compact (b i) hs) hε t x (w i) (hw i)))

theorem generatorRecombine_stack (A : Finset SL(2,ℤ)) (b : ι → Branch)
    (w : ι → List SL(2,ℤ)) (hw : ∀ i a, a ∈ w i → a ∈ A) (c : ι → ℂ)
    {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u)
    (hsub : ∀ i, region (w i) (image (b i) s) ⊆ u)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    (generatorRecombine A b w hw c hs hε t Ds Db x).comp
      (stack (generatorRows A (family b c hs hε t x) hu hε t x)) =
      (QuantitativeSpectralExceptionalUnweight.unweight hε t Ds x).comp (family b c hs hε t x) +
        correctionFamily b (fun i => (w i).prod) c hs hε t Db x := by
  have hp : (PiLp.proj 2 (fun _ : Option ↥A => Space) none).comp
      (stack (generatorRows A (family b c hs hε t x) hu hε t x)) = family b c hs hε t x := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  simp only [generatorRecombine,add_comp,finsetSum_comp,smul_comp,comp_assoc,hp,
    wordRecombine_stack A _ _ _ _ hu (hsub _) hε t x,correctionFamily,correction]

theorem generatorRecombine_norm (A : Finset SL(2,ℤ)) (b : ι → Branch)
    (w : ι → List SL(2,ℤ)) (hw : ∀ i a, a ∈ w i → a ∈ A) (c : ι → ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    ‖generatorRecombine A b w hw c hs hε t Ds Db x‖ ≤
      Ds.bound + ∑ i, ‖c i‖ * (Db i).bound * cost (w i) (image_compact (b i) hs) hε t := by
  apply opNorm_le_bound _ (add_nonneg Ds.bound_nonneg (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (Db i).bound_nonneg) (cost_nonneg _ _ _ _))))
  intro v
  simp only [generatorRecombine,_root_.add_apply,_root_.sum_apply,smul_apply,comp_apply,
    PiLp.proj_apply,add_mul,Finset.sum_mul]
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
      (QuantitativeSpectralExceptionalUnweight.unweight hε t (Db i) x
        (wordRecombine A (image_compact (b i) hs) hε t x (w i) (hw i) v))
    simp only [one_mul] at hp
    have hu := (QuantitativeSpectralExceptionalUnweight.unweight hε t (Db i) x).le_of_opNorm_le
      (QuantitativeSpectralExceptionalUnweight.unweight_norm hε t (Db i) x)
      (wordRecombine A (image_compact (b i) hs) hε t x (w i) (hw i) v)
    have hl := (wordRecombine A (image_compact (b i) hs) hε t x (w i) (hw i)).le_of_opNorm_le
      (wordRecombine_norm A (w i) (hw i) (image_compact (b i) hs) hε t x) v
    have hh := (hp.trans hu).trans (mul_le_mul_of_nonneg_left hl (Db i).bound_nonneg)
    exact (mul_le_mul_of_nonneg_left hh (norm_nonneg (c i))).trans_eq (by ring)

/-- Actual FD sampling factors through the original row and actual fixed
generator defects on a proved common compact region. -/
theorem fundamental_generator_factorization (N : ℕ) (hN : 0 < N) (H : ℝ)
    (A : Finset SL(2,ℤ)) (b : ι → Branch) (w : ι → List SL(2,ℤ))
    (hw : ∀ i a, a ∈ w i → a ∈ A) (c : ι → ℂ)
    {s u E : Set ℍ} (hs : IsCompact s) (hu : IsCompact u) (hEs : E ⊆ s)
    (hsub : ∀ i, region (w i) (image (b i) s) ⊆ u)
    (hred : ∀ i z, z ∈ E → (AsymptoticCongruenceLabels.integralLabel (w i).prod * label (b i)) • z ∈ fundamentalCompact N H)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    (corner E x).comp (fundamentalReducedFamily N hN H b (fun i => (w i).prod) c hε t x) =
      ((corner E x).comp (generatorRecombine A b w hw c hs hε t Ds Db x)).comp
        (stack (generatorRows A (family b c hs hε t x) hu hε t x)) := by
  rw [comp_assoc,generatorRecombine_stack A b w hw c hs hu hsub hε t Ds Db x]
  exact fundamental_retained_identity N hN H b _ c hs hEs hred hε t Ds Db x

#print axioms generatorRecombine_stack
#print axioms generatorRecombine_norm
#print axioms fundamental_generator_factorization

end QuantitativeSpectralExceptionalReducedRows
