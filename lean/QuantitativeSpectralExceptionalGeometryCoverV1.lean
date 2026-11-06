module

public import QuantitativeSpectralExceptionalGeometryStripV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGeometry

open Matrix UpperHalfPlane Set AsymptoticRegularBranchFamily
open AsymptoticRationalFreeness AsymptoticRationalBranches AsymptoticCongruenceLabels
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction
open QuantitativeSpectralExceptionalReducedRows
open scoped MatrixGroups Pointwise

def rightIntegral (b : Branch) (U : SL(2,ℤ)) : Branch where
  matrix := b.matrix * rationalGL U
  positive := by
    simpa only [realMatrix,map_mul,Units.val_mul] using
      mul_pos b.positive (rationalGL_positive U)

theorem rightIntegral_action (b : Branch) (U : SL(2,ℤ)) (z : ℍ) :
    label (rightIntegral b U) • z = label b • (integralLabel U • z) := by
  change ofMatrix (b.matrix * rationalGL U) (rightIntegral b U).positive • z =
    ofMatrix b.matrix b.positive • (ofMatrix (rationalGL U) (rationalGL_positive U) • z)
  calc
    _ = realMatrix (b.matrix * rationalGL U) • z :=
      ofMatrix_action _ (rightIntegral b U).positive z
    _ = realMatrix b.matrix • (realMatrix (rationalGL U) • z) := by
      change (GeneralLinearGroup.map (algebraMap ℚ ℝ) (b.matrix * rationalGL U)) • z = _
      rw [map_mul,mul_smul]
      rfl
    _ = _ := by rw [ofMatrix_action,ofMatrix_action]

/-- The finite quotient cusp charts and the actual rational affine cusp
reductions give one word set and one linear height loss for the entire
growing compact quotient cover, not just for a fixed compact core. -/
theorem finite_cover_family_words {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    (b : ι → Branch) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∃ W : Finset (List SL(2,ℤ)),
      (∀ l ∈ W, ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S) ∧
      ∀ H : ℝ, B ≤ H → ∀ z ∈ wideCompactCover N (H/C), ∀ i,
        ∃ l ∈ W, (integralLabel l.prod * label (b i)) • z ∈ wideCompactCover N H := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  let Q := SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N
  let := Fintype.ofFinite Q
  let f : (ι × Q) → Branch := fun iq => rightIntegral (b iq.1) iq.2.out⁻¹
  obtain ⟨C,B,hC,hB,W,hW,hr⟩ := finite_strip_family_words N S hS f 2
    (show (0:ℝ) < 1/4 by norm_num)
  refine ⟨C,B,hC,hB,W,hW,?_⟩
  intro H hH z hz i
  obtain ⟨q,v,hv,rfl⟩ := mem_iUnion.mp hz
  have hx : |v.re| ≤ 2 := abs_le.mpr ⟨by linarith [hv.1],hv.2.1⟩
  obtain ⟨l,hl,hlv⟩ := hr H hH v hx hv.2.2.1 hv.2.2.2 (i,q)
  refine ⟨l,hl,?_⟩
  simpa only [f,mul_smul,rightIntegral_action,map_inv] using hlv

/-- The precise retained open-cover geometric input required by the
exceptional row factorization follows with no extra reduction assumption.
Only the output cusp tail at H/C is removed. -/
theorem finite_retained_family_words {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    (b : ι → Branch) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∃ W : Finset (List SL(2,ℤ)),
      (∀ l ∈ W, ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S) ∧
      ∀ H : ℝ, B ≤ H → ∀ z ∈ openCover N \ wideTailCover N (H/C), ∀ i,
        ∃ l ∈ W, (integralLabel l.prod * label (b i)) • z ∈ wideCompactCover N H := by
  obtain ⟨C,B,hC,hB,W,hW,hr⟩ := finite_cover_family_words N hN S hS b
  refine ⟨C,B,hC,hB,W,hW,?_⟩
  intro H hH z hz i
  have hh := openCover_subset_wide_split N (H/C) hz.1
  exact hr H hH z (hh.resolve_right hz.2) i

#print axioms finite_cover_family_words
#print axioms finite_retained_family_words

end QuantitativeSpectralExceptionalGeometry
