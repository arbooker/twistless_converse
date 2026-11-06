module

public import QuantitativeHolomorphicCompactDataV1
public import QuantitativeHolomorphicCertificateHeightV1
public import QuantitativeEulerCompactIntegerHeightV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane MeasureTheory AsymptoticRationalFreeness
open AsymptoticCompactBranch AsymptoticFiniteBranch

/-- Capped powers retain an explicit bound under a height distortion.
No compactness choice enters this estimate. -/
theorem compact_ratio_le_of_height (g : GL (Fin 2) ℝ) {ε C : ℝ}
    (hε : 0<ε) (hC : 1≤C) (t : ℕ) (z : ℍ)
    (hz : z.im≤C*(g • z).im) : ratio g ε t z≤C^t := by
  let a := min (z.im/ε) 1
  let b := min ((g • z).im/ε) 1
  have ha : 0<a := lt_min (div_pos z.im_pos hε) zero_lt_one
  have hb : 0<b := lt_min (div_pos (g • z).im_pos hε) zero_lt_one
  have hab : a≤C*b := by
    by_cases hg : (g • z).im/ε≤1
    · have he : b=(g • z).im/ε := min_eq_left hg
      rw [he]
      apply (min_le_left _ _).trans
      calc
        z.im/ε ≤ (C*(g • z).im)/ε := div_le_div_of_nonneg_right hz hε.le
        _ = C*((g • z).im/ε) := by ring
    · have he : b=1 := min_eq_right (le_of_not_ge hg)
      rw [he,mul_one]
      exact (min_le_right _ _).trans hC
  change a^t/b^t≤C^t
  apply (div_le_iff₀ (pow_pos hb t)).mpr
  simpa only [mul_pow] using (pow_le_pow_left₀ ha.le hab t)

/-- The required height distortion follows directly from the actual
Möbius denominator and determinant, with no qualitative boundedness. -/
theorem compact_ratio_le_of_denominator (g : GL (Fin 2) ℝ) {ε C : ℝ}
    (hε : 0<ε) (hC : 1≤C) (t : ℕ) (z : ℍ)
    (hz : Complex.normSq (denom g z)≤C*|g.det.val|) : ratio g ε t z≤C^t := by
  apply compact_ratio_le_of_height g hε hC t z
  rw [im_smul_eq_div_normSq]
  have hd : 0<Complex.normSq (denom g z) := normSq_denom_pos g z.im_ne_zero
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hd).mpr
  nlinarith [mul_le_mul_of_nonneg_right hz z.im_pos.le]

/-- An explicit symmetric fold interval and ratio bound are legitimate
compact branch data. These data can replace the old compactness choice by
`physical_compact_data_independent` and `regular_compact_data_independent`. -/
def boundedCompactData (g : GL (Fin 2) ℝ) {s : Set ℍ} {ε C : ℝ}
    (hε : 0<ε) (hC : 1≤C) (t J : ℕ)
    (hre : ∀ z∈s, |(g • z).re|≤(J:ℝ))
    (hden : ∀ z∈s, Complex.normSq (denom g z)≤C*|g.det.val|) : Data g s ε t where
  folds := Finset.Icc (-(J:ℤ)) J
  fold_mem := by
    intro z hz
    apply Finset.mem_Icc.mpr
    have hh := abs_le.mp (hre z hz)
    constructor
    · apply Int.le_floor.mpr
      simpa only [Int.cast_neg,Int.cast_natCast] using hh.1
    · have h := Int.floor_mono hh.2
      simpa using h
  bound := C^t
  bound_nonneg := pow_nonneg (zero_le_one.trans hC) t
  ratio_le := fun z hz => compact_ratio_le_of_denominator g hε hC t z (hden z hz)


/-- An explicit lower bound on the image height bounds the capped weight
ratio, uniformly over the source height. -/
theorem compact_ratio_bound (g : GL (Fin 2) ℝ) {ε η : ℝ}
    (hε : 0<ε) (hη : 0<η) (t : ℕ) (z : UpperHalfPlane)
    (hz : η ≤ (g • z).im) :
    ratio g ε t z ≤ ((min (η/ε) 1)^t)⁻¹ := by
  have hm : 0 < min (η/ε) 1 := lt_min (div_pos hη hε) zero_lt_one
  have hn : cap ε t z ≤ 1 := by
    exact pow_le_one₀ (le_of_lt (lt_min (div_pos z.im_pos hε) zero_lt_one))
      (min_le_right _ _)
  have hd : (min (η/ε) 1)^t ≤ cap ε t (g • z) := by
    exact pow_le_pow_left₀ hm.le (min_le_min_right 1 (div_le_div_of_nonneg_right hz hε.le)) t
  unfold ratio
  calc
    _ ≤ 1 / cap ε t (g • z) := div_le_div_of_nonneg_right hn (cap_pos hε t _).le
    _ ≤ 1 / (min (η/ε) 1)^t := one_div_le_one_div_of_le (pow_pos hm t) hd
    _ = _ := one_div _

/-- Concrete compact metadata: exactly `2J+1` folds and an explicit capped
weight bound. Only coordinate bounds for the image region are required. -/
def imageBoundedCompactData (g : GL (Fin 2) ℝ) (s : Set UpperHalfPlane)
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) (t J : ℕ)
    (hre : ∀ z∈s, |(g • z).re| ≤ J)
    (him : ∀ z∈s, η ≤ (g • z).im) : Data g s ε t where
  folds := Finset.Icc (-(J:ℤ)) J
  fold_mem := by
    intro z hz
    have hh := abs_le.mp (hre z hz)
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      simpa using hh.1
    · simpa using Int.floor_mono hh.2
  bound := ((min (η/ε) 1)^t)⁻¹
  bound_nonneg := by positivity
  ratio_le := fun z hz => compact_ratio_bound g hε hη t z (him z hz)

theorem imageBoundedCompactData_card (g : GL (Fin 2) ℝ) (s : Set UpperHalfPlane)
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) (t J : ℕ)
    (hre : ∀ z∈s, |(g • z).re| ≤ J)
    (him : ∀ z∈s, η ≤ (g • z).im) :
    (imageBoundedCompactData g s hε hη t J hre him).folds.card = 2*J+1 := by
  simp [imageBoundedCompactData, Int.card_Icc]
  omega

/-- Translating a literal observation matrix has only linear entry-height
cost. The representation holds globally, not merely on the compact set. -/
theorem compactFold_integer_height (g : GL (Fin 2) ℚ)
    (hg : 0<(realMatrix g).det.val) {M : IntegerMatrix2} {B : ℝ}
    (hM : IntegerAction (AsymptoticRationalBranches.ofMatrix g hg) M)
    (hB : MatrixEntryBound M B) (n : ℤ) :
    ∃ Mn : IntegerMatrix2,
      IntegerAction (AsymptoticRationalBranches.compactFold g hg n) Mn ∧
        MatrixEntryBound Mn (2*(1+|(n:ℝ)|)*B) :=
  QuantitativeEulerIntegerHeight.compactFold_integer_height g hg hM hB n

/-- Explicit matrix-height certificate for a bounded compact observation.
The old arbitrary compact metadata is replaced by the coordinate cutoffs. -/
theorem boundedCompactExpression_matrix_bound (g : GL (Fin 2) ℚ)
    (hg : 0<(realMatrix g).det.val) {s : Set UpperHalfPlane} (hs : MeasurableSet s)
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) (t J : ℕ)
    (hre : ∀ z∈s, |(realMatrix g • z).re| ≤ J)
    (him : ∀ z∈s, η ≤ (realMatrix g • z).im)
    {M : IntegerMatrix2} {B : ℝ} (hB0 : 0≤B)
    (hM : IntegerAction (AsymptoticRationalBranches.ofMatrix g hg) M)
    (hB : MatrixEntryBound M B) :
    ExpressionMatrixBound (compactExpression g hg hs hε t
      (imageBoundedCompactData (realMatrix g) s hε hη t J hre him))
      (4*(1+(J:ℝ))*B) := by
  have hraw : ExpressionMatrixBound (compactRawExpression g hg hs hε t
      (imageBoundedCompactData (realMatrix g) s hε hη t J hre him)) (2*(1+(J:ℝ))*B) := by
    intro b hb
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hb
    have hn' : n ∈ Finset.Icc (-(J:ℤ)) J := Finset.mem_toList.mp hn
    obtain ⟨L,hl,hL⟩ := compactFold_integer_height g hg hM hB n
    have hnJ : |(n:ℝ)|≤J := by
      have hh := Finset.mem_Icc.mp hn'
      apply abs_le.mpr
      constructor
      · exact_mod_cast hh.1
      · exact_mod_cast hh.2
    refine ⟨L,hl,fun a b => (hL a b).trans ?_⟩
    nlinarith
  have hh := hraw.compose (expressionMatrixBound_singleton_one
    (corner AsymptoticMassTransport.strip AsymptoticMassTransport.strip_measurable) rfl) zero_le_one
  convert hh using 1
  · rfl
  · ring

#print axioms compact_ratio_le_of_height
#print axioms compact_ratio_le_of_denominator
#print axioms boundedCompactData
#print axioms compact_ratio_bound
#print axioms imageBoundedCompactData_card
#print axioms compactFold_integer_height
#print axioms boundedCompactExpression_matrix_bound

end QuantitativeHolomorphic
