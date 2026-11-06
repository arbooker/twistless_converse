module

public import QuantitativeEulerEndpointCommonRowsV1
public import QuantitativeEulerEndpointInverseRegionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeHolomorphic QuantitativeArithmetic
open QuantitativeEulerDiamondDecode QuantitativeEulerDensityGenerators
open AsymptoticIntegralSubgroup AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticFreshAveraging AsymptoticFreshCompactDefects
open AsymptoticRegularBranchFamily AsymptoticRegularObservationRows AsymptoticCompactFamilyTranslation
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

theorem rectangle_subset_shifted {R Y H : ℝ} (r : ℚ) (hr : |(r : ℝ)|≤1) :
    observationRectangle R Y H⊆shifted r (observationRectangle (R+1) Y H) := by
  intro z hz
  let u := (translationLabel r)⁻¹ • z
  have he : translationLabel r • u=z := smul_inv_smul _ _
  have hre := rational_translation_re r u
  have him := AsymptoticCompactTranslation.label_im r u
  rw [he] at hre him
  have hu : u.re=z.re-(r : ℝ) := by linarith
  refine ⟨u,⟨?_,?_,?_⟩,he⟩
  · rw [hu]
    exact (abs_sub _ _).trans (add_le_add hz.1 hr)
  · exact him ▸ hz.2.1
  · exact him ▸ hz.2.2

theorem parameter_abs_le_one (q : ℕ) [Fact q.Prime] (j : Fin (q-1)) :
    |(parameter q j : ℝ)|≤1 := by
  have hq : (0 : ℝ)<q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hj : j.val+1≤q := by omega
  have hjr : (j.val : ℝ)+1≤q := by exact_mod_cast hj
  change |((((j.val+1 : ℕ) : ℚ)/q : ℚ) : ℝ)|≤1
  push_cast
  rw [abs_of_nonneg (div_nonneg (by positivity) hq.le)]
  exact (div_le_one hq).2 hjr

/-- One extra unit of width lets EVERY individual fresh row use its
required shifted cutoff, while preserving the exact averaging identity. -/
def freshObservationRegion (B Y H : ℝ) : Set ℍ :=
  observationRectangle (B*(H+2)/min 1 Y+1) (Y/integerCompactDistortion B H)
    (B*(H+2)/min 1 Y)

theorem freshObservationRegion_compact (B H : ℝ) {Y : ℝ} (hY : 0<Y) :
    IsCompact (freshObservationRegion B Y H) :=
  observationRectangle_compact _ _ (div_pos hY (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

theorem common_subset_fresh (B Y H : ℝ) : commonImageRegion B Y H⊆freshObservationRegion B Y H := by
  intro z hz
  exact ⟨hz.1.trans (by linarith),hz.2⟩

theorem common_subset_fresh_shifted (B Y H : ℝ) (q : ℕ) [Fact q.Prime] (j : Fin (q-1)) :
    commonImageRegion B Y H⊆shifted (parameter q j) (freshObservationRegion B Y H) :=
  rectangle_subset_shifted _ (parameter_abs_le_one q j)

theorem compact_prime_residual_eq (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (j : Fin (q-1)) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x (w • symbol (defectLabel N q hN hq j)-1)=
      w • compact (matrixBranch N q hN hq j) hs hε t x-compact identityBranch hs hε t x := by
  have hm := compactAction_branch hs hε t x (matrixBranch N q hN hq j)
  rw [matrixBranch_label] at hm
  have hi := compactAction_branch hs hε t x identityBranch
  rw [identityBranch_label,map_one] at hi
  calc
    _ = w • compactAction hs hε t x (symbol (defectLabel N q hN hq j))-
        compactAction hs hε t x 1 := by rw [map_sub,map_smul]
    _ = _ := congrArg₂ (fun L R : Space →L[ℂ] Space => L-R)
      (congrArg (fun L : Space →L[ℂ] Space => w • L) hm) hi

theorem prime_residual_restrict_norm (N q : ℕ) [Fact q.Prime]
    (hN : 0<N) (hq : ¬q∣N) (j : Fin (q-1)) (w : ℂ)
    {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u) (hsu : s⊆u)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖(w • compact (matrixBranch N q hN hq j) hs hε t x-compact identityBranch hs hε t x) v‖≤
    ‖(w • compact (matrixBranch N q hN hq j) hu hε t x-compact identityBranch hu hε t x) v‖ := by
  have h1 := congrArg (fun T : Space →L[ℂ] Space => ‖T v‖)
    (compact_prime_residual_eq N q hN hq j w hs hε t x)
  have h2 := congrArg (fun T : Space →L[ℂ] Space => ‖T v‖)
    (compact_prime_residual_eq N q hN hq j w hu hε t x)
  exact (h1.symm.trans_le (compactAction_restrict_norm _ hs hu hsu hε t x v)).trans_eq h2

theorem fricke_row_restrict_norm (N : ℕ) (hN : 0<N) (w : ℂ)
    {s u : Set ℍ} (hs : IsCompact s) (hu : IsCompact u) (hsu : s⊆u)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖twist N 1 hN Nat.zero_lt_one w hs hε t x v‖≤
    ‖twist N 1 hN Nat.zero_lt_one w hu hε t x v‖ := by
  have h1 := congrArg (fun T : Space →L[ℂ] Space => ‖T v‖)
    (compactAction_untwisted N hN w hs hε t x)
  have h2 := congrArg (fun T : Space →L[ℂ] Space => ‖T v‖)
    (compactAction_untwisted N hN w hu hε t x)
  exact (h1.symm.trans_le (compactAction_restrict_norm _ hs hu hsu hε t x v)).trans_eq h2

#print axioms rectangle_subset_shifted
#print axioms common_subset_fresh_shifted
#print axioms prime_residual_restrict_norm
#print axioms fricke_row_restrict_norm
end QuantitativeEulerEndpointPrepared
