module

public import QuantitativeSpectralExceptionalReducedRowsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticRegularBranchFamily AsymptoticRegularObservationRows
open AsymptoticCongruenceLabels
open QuantitativeSpectralExceptionalUnweight (G Space)
open QuantitativeSpectralObservability QuantitativeSpectralObservabilityDecoded
open scoped lp MatrixGroups

variable {ι : Type*} [Fintype ι]

/-- A finite rational row sampled at its explicitly reduced coordinates. -/
def reducedFamily (N : ℕ) (hN : 0 < N) (H : ℝ) (b : ι → Branch)
    (γ : ι → SL(2,ℤ)) (c : ι → ℂ) {ε : ℝ} (hε : 0 < ε) (t : ℕ) (x : ℍ) :
    Space →L[ℂ] Space :=
  ∑ i, c i • (pull (integralLabel (γ i) * label (b i))).comp (sampling N hN H hε t x)

/-- The correction consists of actual integral modular defects, one for
each reducing word, pulled back by its original rational branch. -/
def correctionFamily (b : ι → Branch) (γ : ι → SL(2,ℤ)) (c : ι → ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t)
    (x : ℍ) : Space →L[ℂ] Space :=
  ∑ i, c i • correction (b i) (γ i) hs hε t (D i) x

/-- Exact retained-row identity. The RHS uses the original literal
compact rational residual family, plus genuine modular defects of the
chosen reducing matrices. No equality of residual operators is assumed. -/
theorem retained_family_identity (N : ℕ) (hN : 0 < N) (H : ℝ)
    (b : ι → Branch) (γ : ι → SL(2,ℤ)) (c : ι → ℂ)
    {s E : Set ℍ} (hs : IsCompact s) (hEs : E ⊆ s)
    (hred : ∀ i z, z ∈ E → (integralLabel (γ i) * label (b i)) • z ∈ wideCompactCover N H)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner E x).comp (reducedFamily N hN H b γ c hε t x) =
    (AsymptoticOrbitDiagonal.corner E x).comp
      ((QuantitativeSpectralExceptionalUnweight.unweight hε t Ds x).comp (family b c hs hε t x) +
        correctionFamily b γ c hs hε t Db x) := by
  calc
    _ = ∑ i, c i • (AsymptoticOrbitDiagonal.corner E x).comp
        ((pull (integralLabel (γ i) * label (b i))).comp (sampling N hN H hε t x)) := by
      simp only [reducedFamily, comp_finsetSum, comp_smul]
    _ = ∑ i, c i • (AsymptoticOrbitDiagonal.corner E x).comp
        (rawBranch (b i) hs hε t Ds x + correction (b i) (γ i) hs hε t (Db i) x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [retained_branch_identity N hN H (b i) (γ i) hs hEs (hred i) hε t Ds (Db i) x]
    _ = _ := by
      simp only [family, correctionFamily, rawBranch, comp_add, comp_finsetSum, comp_smul,
        smul_add, Finset.sum_add_distrib]

/-- Explicit bound on the true modular-defect recombination. -/
theorem correctionFamily_norm (b : ι → Branch) (γ : ι → SL(2,ℤ)) (c : ι → ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (D : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (b i) s) ε t) (x : ℍ) :
    ‖correctionFamily b γ c hs hε t D x‖ ≤
      ∑ i, ‖c i‖ * ((D i).bound * AsymptoticCongruenceDefect.bound (γ i) (image_compact (b i) hs) hε t) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (correction_norm (b i) (γ i) hs hε t (D i) x) (norm_nonneg _)

/-- Literal initial twist rows satisfy the retained reduction formula. -/
theorem retained_twist_identity (N q : ℕ) (hN : 0 < N) (hq : 0 < q) (H : ℝ) (χ : ℂ)
    (γ : (AsymptoticCertificateBranches.residues q ⊕ AsymptoticCertificateBranches.residues q) → SL(2,ℤ))
    {s E : Set ℍ} (hs : IsCompact s) (hEs : E ⊆ s)
    (hred : ∀ i z, z ∈ E → (integralLabel (γ i) * label (twistBranches N q hN hq i)) • z ∈ wideCompactCover N H)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (twistBranches N q hN hq i) s) ε t)
    (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner E x).comp
      (reducedFamily N hN H (twistBranches N q hN hq) γ (Sum.elim (fun _ => 1) (fun _ => -χ)) hε t x) =
    (AsymptoticOrbitDiagonal.corner E x).comp
      ((QuantitativeSpectralExceptionalUnweight.unweight hε t Ds x).comp (twist N q hN hq χ hs hε t x) +
        correctionFamily (twistBranches N q hN hq) γ (Sum.elim (fun _ => 1) (fun _ => -χ)) hs hε t Db x) :=
  retained_family_identity N hN H _ γ _ hs hEs hred hε t Ds Db x

/-- Literal ramified initial rows satisfy the same exact reduction formula. -/
theorem retained_bad_identity (N p : ℕ) (hN : 0 < N) (hp : 0 < p) (H : ℝ) (δ : ℂ)
    (γ : (Fin p ⊕ Unit) → SL(2,ℤ)) {s E : Set ℍ} (hs : IsCompact s) (hEs : E ⊆ s)
    (hred : ∀ i z, z ∈ E → (integralLabel (γ i) * label (ramifiedBranches p hp i)) • z ∈ wideCompactCover N H)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ)
    (Ds : QuantitativeSpectralExceptionalUnweight.Data s ε t)
    (Db : ∀ i, QuantitativeSpectralExceptionalUnweight.Data (image (ramifiedBranches p hp i) s) ε t)
    (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner E x).comp
      (reducedFamily N hN H (ramifiedBranches p hp) γ (Sum.elim (fun _ => 1) (fun _ => -δ)) hε t x) =
    (AsymptoticOrbitDiagonal.corner E x).comp
      ((QuantitativeSpectralExceptionalUnweight.unweight hε t Ds x).comp (bad p hp δ hs hε t x) +
        correctionFamily (ramifiedBranches p hp) γ (Sum.elim (fun _ => 1) (fun _ => -δ)) hs hε t Db x) :=
  retained_family_identity N hN H _ γ _ hs hEs hred hε t Ds Db x

#print axioms retained_family_identity
#print axioms correctionFamily_norm
#print axioms retained_twist_identity
#print axioms retained_bad_identity

end QuantitativeSpectralExceptionalReducedRows
