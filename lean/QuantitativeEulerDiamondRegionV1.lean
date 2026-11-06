module

public import QuantitativeEulerDiamondMultiplierV1
public import AsymptoticCongruenceDefectV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open UpperHalfPlane AsymptoticCongruenceLabels AsymptoticOrbitDecode
open QuantitativeHolomorphic AsymptoticRegularCompactBranch
open AsymptoticCompactBranch (cap)
open scoped Classical MatrixGroups

/-- The group-algebra congruence residual is the original compact
congruence-defect operator, including the actual strip fold and cap. -/
theorem compactAction_congruence (γ : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x (symbol (integralLabel γ)-1)=
      AsymptoticCongruenceDefect.operator γ hs hε t x := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext a
  rw [compactAction_decode,AsymptoticCongruenceDefect.operator_decode]
  simp only [decodedEvaluation,map_sub,evaluate_symbol,evaluate_one,one_mul]

theorem compactAction_restrict (A : Ring) {s u : Set ℍ}
    (hs : IsCompact s) (hu : IsCompact u) (hsub : s⊆u)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    (AsymptoticOrbitDiagonal.corner s x).comp (compactAction hu hε t x A)=
      compactAction hs hε t x A := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext a
  simp only [ContinuousLinearMap.comp_apply,AsymptoticOrbitDiagonal.corner_apply,
    compactAction_decode]
  by_cases ha : a • x∈s
  · simp only [ite_eq_left ha,ite_eq_left (hsub ha)]
  · simp only [ite_eq_right ha]

theorem compactAction_restrict_norm (A : Ring) {s u : Set ℍ}
    (hs : IsCompact s) (hu : IsCompact u) (hsub : s⊆u)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x A v‖≤‖compactAction hu hε t x A v‖ := by
  rw [←compactAction_restrict A hs hu hsub hε t x,ContinuousLinearMap.comp_apply]
  simpa only [one_mul] using (AsymptoticOrbitDiagonal.corner s x).le_of_opNorm_le
    (AsymptoticOrbitRegion.corner_norm_le s x) (compactAction hu hε t x A v)

def multiplierRegion (B : Ring) (s : Set ℍ) : Set ℍ :=
  ⋃ g : ↥B.coeff.support, branchImage (symbolBranch g) s

theorem multiplierRegion_compact (B : Ring) {s : Set ℍ} (hs : IsCompact s) :
    IsCompact (multiplierRegion B s) :=
  isCompact_iUnion (fun g => branchImage_compact (symbolBranch g) hs)

theorem branchImage_subset_multiplierRegion (B : Ring) (g : G) (hg : g∈B.coeff.support)
    (s : Set ℍ) : branchImage (symbolBranch g) s⊆multiplierRegion B s :=
  Set.subset_iUnion_of_subset ⟨g,hg⟩ (Set.Subset.refl _)

/-- An unconditional residual inequality on one explicit compact region.
The scalar polynomial constant is fixed before all cutoff parameters and
before the expression whose residual is being observed. -/
theorem fixed_multiplier_region_bound (B : Ring) :
    ∃ C : ℝ, 1≤C ∧ ∀ (A : Ring) {s : Set ℍ} (hs : IsCompact s)
      {ε : ℝ} (hε : 0<ε) (H : ℝ)
      (_hre : ∀ z∈s, |z.re|≤1) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
      ‖compactAction hs hε t x (A*B) v‖≤
        expressionMass B*(integerCompactDistortion C H)^t*
          ‖compactAction (multiplierRegion_compact B hs) hε t x A v‖ := by
  obtain ⟨C,hC,hbound⟩ := fixed_multiplier_polynomial_bound B
  refine ⟨C,hC,?_⟩
  intro A s hs ε hε H hre him t x v
  apply hbound A hs hε H hre him t x v
  intro g hg
  exact compactAction_restrict_norm A (branchImage_compact (symbolBranch g) hs)
    (multiplierRegion_compact B hs) (branchImage_subset_multiplierRegion B g hg s) hε t x v

#print axioms compactAction_congruence
#print axioms compactAction_restrict_norm
#print axioms fixed_multiplier_region_bound
end QuantitativeEulerDiamondDecode
