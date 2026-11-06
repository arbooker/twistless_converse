module

public import QuantitativeSpectralExceptionalGeneratorRowsV1
public import QuantitativeSpectralExceptionalFundamentalPartitionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane ContinuousLinearMap AsymptoticObservationStack AsymptoticRegularBranchFamily
open AsymptoticOrbitDiagonal QuantitativeSpectralWordDefect
open QuantitativeSpectralExceptionalUnweight (G Space)
open QuantitativeSpectralObservability
open scoped MatrixGroups lp

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- All intermediate images used by the finitely many chosen words. -/
def commonRegion (b : ι → Branch) (w : κ → ι → List SL(2,ℤ)) (s : Set ℍ) : Set ℍ :=
  ⋃ j, ⋃ i, region (w j i) (image (b i) s)

theorem commonRegion_compact (b : ι → Branch) (w : κ → ι → List SL(2,ℤ))
    {s : Set ℍ} (hs : IsCompact s) : IsCompact (commonRegion b w s) :=
  isCompact_iUnion (fun j => isCompact_iUnion (fun i =>
    region_compact (w j i) (image_compact (b i) hs)))

omit [Fintype ι] [Fintype κ] in
theorem region_subset_common (b : ι → Branch) (w : κ → ι → List SL(2,ℤ))
    (s : Set ℍ) (j : κ) (i : ι) : region (w j i) (image (b i) s) ⊆ commonRegion b w s :=
  fun _ hz => Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨i,hz⟩⟩

/-- Actual finite piece selection of reduced FD-sampled row values. -/
def selectedFundamentalFamily (N : ℕ) (hN : 0 < N) (H : ℝ)
    (b : ι → Branch) (w : κ → ι → List SL(2,ℤ)) (c : ι → ℂ) (E : κ → Set ℍ)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  ∑ j, (corner (E j) x).comp
    (fundamentalReducedFamily N hN H b (fun i => (w j i).prod) c hε t x)

def selectedGeneratorRecombine (A : Finset SL(2,ℤ)) (b : ι → Branch)
    (w : κ → ι → List SL(2,ℤ)) (hw : ∀ j i a, a ∈ w j i → a ∈ A)
    (c : ι → ℂ) (E : κ → Set ℍ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    GeneratorData A →L[ℂ] Space :=
  ∑ j, (corner (E j) x).comp (generatorRecombine A b (w j) (hw j) c hs hε t Ds Db x)

/-- One shared stack of the original rational residual and actual fixed
generator defects suffices for every selected piece. -/
def commonResidualStack (A : Finset SL(2,ℤ)) (b : ι → Branch)
    (w : κ → ι → List SL(2,ℤ)) (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] GeneratorData A :=
  stack (generatorRows A (family b c hs hε t x) (commonRegion_compact b w hs) hε t x)

theorem selected_generator_factorization (N : ℕ) (hN : 0 < N) (H : ℝ)
    (A : Finset SL(2,ℤ)) (b : ι → Branch) (w : κ → ι → List SL(2,ℤ))
    (hw : ∀ j i a, a ∈ w j i → a ∈ A) (c : ι → ℂ) (E : κ → Set ℍ)
    {s : Set ℍ} (hs : IsCompact s) (hEs : ∀ j, E j ⊆ s)
    (hred : ∀ j i z, z ∈ E j →
      (AsymptoticCongruenceLabels.integralLabel (w j i).prod*label (b i)) • z ∈ fundamentalCompact N H)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    selectedFundamentalFamily N hN H b w c E hε t x =
      (selectedGeneratorRecombine A b w hw c E hs hε t Ds Db x).comp
        (commonResidualStack A b w c hs hε t x) := by
  simp only [selectedFundamentalFamily,selectedGeneratorRecombine,finsetSum_comp,commonResidualStack]
  apply Finset.sum_congr rfl
  intro j _
  exact fundamental_generator_factorization N hN H A b (w j) (hw j) c hs
    (commonRegion_compact b w hs) (hEs j) (region_subset_common b w s j) (hred j) hε t Ds Db x

/-- Explicit boundedness of the assembled recombination, with all cap and
word-transport costs displayed. Its number of terms is fixed geometrically. -/
theorem selectedGeneratorRecombine_norm (A : Finset SL(2,ℤ)) (b : ι → Branch)
    (w : κ → ι → List SL(2,ℤ)) (hw : ∀ j i a, a ∈ w j i → a ∈ A)
    (c : ι → ℂ) (E : κ → Set ℍ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    ‖selectedGeneratorRecombine A b w hw c E hs hε t Ds Db x‖ ≤
      ∑ j, (Ds.bound + ∑ i, ‖c i‖*(Db i).bound*cost (w j i) (image_compact (b i) hs) hε t) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (opNorm_comp_le _ _).trans
  apply ((mul_le_mul_of_nonneg_right (AsymptoticOrbitRegion.corner_norm_le _ _) (norm_nonneg _))).trans
  simpa only [one_mul] using generatorRecombine_norm A b (w j) (hw j) c hs hε t Ds Db x

#print axioms selected_generator_factorization
#print axioms selectedGeneratorRecombine_norm

end QuantitativeSpectralExceptionalReducedRows
