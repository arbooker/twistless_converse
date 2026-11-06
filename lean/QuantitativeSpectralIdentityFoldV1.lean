module

public import QuantitativeSpectralDecodedSamplingV1
public import QuantitativeSpectralModularCoordinateV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralIdentityFold

open MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticRegularBranchFamily AsymptoticFreshCompactDefects AsymptoticOrbitDecode
open AsymptoticRationalFreeness AsymptoticRationalBranches AsymptoticCompactBranch
open QuantitativeSpectralCoverSampling QuantitativeSpectralDecodedSampling
open QuantitativeSpectralCoverUnweight QuantitativeSpectralCongruenceCover
open QuantitativeSpectralModularCoordinate
open scoped lp

def folds (C : ℝ) : Finset ℤ := Finset.Icc (-Int.ceil C-1) (Int.ceil C+1)

theorem folds_mem {C r : ℝ} (hr : |r| ≤ C) : Int.floor r ∈ folds C := by
  rw [folds, Finset.mem_Icc]
  have hceil := Int.le_ceil C
  have hfloor := Int.floor_le r
  have hlt := Int.lt_floor_add_one r
  constructor
  · have h : ((-Int.ceil C-1 : ℤ):ℝ) ≤ (Int.floor r:ℝ) := by
      push_cast
      linarith [(abs_le.mp hr).1]
    exact_mod_cast h
  · have h : (Int.floor r:ℝ) ≤ ((Int.ceil C+1 : ℤ):ℝ) := by
      push_cast
      linarith [(abs_le.mp hr).2]
    exact_mod_cast h

theorem folds_card {C : ℝ} (hC : 0 ≤ C) : ((folds C).card:ℝ) ≤ 2*C+5 := by
  have hc := Int.ceil_nonneg hC
  have he := Int.card_Icc_of_le (-Int.ceil C-1) (Int.ceil C+1) (show -Int.ceil C-1 ≤ Int.ceil C+1+1 by omega)
  have he' : ((folds C).card:ℝ) = (Int.ceil C:ℝ)+1+1-(-(Int.ceil C:ℝ)-1) := by
    exact_mod_cast he
  rw [he']
  linarith [Int.ceil_lt_add_one C]

theorem identity_action (z : ℍ) : realMatrix identityBranch.matrix • z=z := by
  rw [← ofMatrix_action _ identityBranch.positive,identityBranch_label,one_smul]

/-- Explicit finite-fold certificate for periodic identity sampling. -/
def identityData {s : Set ℍ} {ε C : ℝ} (hε : 0 < ε) (t : ℕ)
    (hC : ∀ z ∈ s, |z.re| ≤ C) : Data (realMatrix identityBranch.matrix) s ε t where
  folds := folds C
  fold_mem z hz := by rw [identity_action]; exact folds_mem (hC z hz)
  bound := 1
  bound_nonneg := zero_le_one
  ratio_le z _ := by rw [ratio,identity_action,div_self (cap_pos hε t z).ne']

/-- The norm of actual folded identity observation has polynomial cost,
independent of the compactness-chosen auxiliary fold certificate. -/
theorem compact_identity_norm {s : Set ℍ} (hs : IsCompact s) {ε C : ℝ}
    (hε : 0 < ε) (t : ℕ) (hC : 0 ≤ C) (hw : ∀ z ∈ s, |z.re| ≤ C) (z : ℍ) :
    ‖compact identityBranch hs hε t z‖ ≤ 2*C+5 := by
  unfold compact
  rw [AsymptoticRegularCompactBranch.operator_data_independent _ _ _ _ _ (identityData hε t hw)]
  apply (AsymptoticRegularCompactBranch.operator_norm_le _ _ _ _ _ _).trans
  simpa only [identityData,mul_one] using folds_card hC

/-- Full periodic decoded sampling now has an explicit polynomial bound
in H, including both the folds and the inverse cap. -/
theorem sampling_polynomial_norm (N : ℕ) (hN : 0 < N) (H : ℝ) (hH : 0 ≤ H)
    {ε : ℝ} (hε : 0 < ε) (t : ℕ) (z : ℍ) :
    ‖sampling N hN H hε t z‖ ≤
      samplingBound N hN H ε t * (8*coverBound N hN*(H+2)+5) := by
  have hC : 0 ≤ 4*coverBound N hN*(H+2) := by
    have hb := coverBound_one_le N hN
    positivity
  have hnorm := compact_identity_norm (compactCover_compact N hN H) hε t hC
    (fun w hw => compactCover_re_bound N hN H hw) z
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul (sampler_norm N hN H hε t z) hnorm (norm_nonneg _)
    (samplingBound_nonneg N hN H ε t)).trans_eq
  congr 1
  ring

#print axioms compact_identity_norm
#print axioms sampling_polynomial_norm

end QuantitativeSpectralIdentityFold
